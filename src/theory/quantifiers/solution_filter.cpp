/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for filtering solutions.
 */

#include "theory/quantifiers/solution_filter.h"

#include <fstream>

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "smt/set_defaults.h"
#include "util/random.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SolutionFilterStrength::SolutionFilterStrength(Env& env)
    : ExprMiner(env), d_isStrong(true)
{
  d_subOptions.copyValues(options());
  smt::SetDefaults::disableChecking(d_subOptions);
}
void SolutionFilterStrength::initialize(const std::vector<Node>& vars,
                                        SygusSampler* ss)
{
  ExprMiner::initialize(vars, ss);
}

void SolutionFilterStrength::setLogicallyStrong(bool isStrong)
{
  d_isStrong = isStrong;
}


bool SolutionFilterStrength::addTerm(Node n, std::vector<Node>& filtered)
{
  return true;
  if (!n.getType().isBoolean())
  {
    // currently, should not register non-Boolean terms here
    std::stringstream ss;
    ss << "SyGuS solution filtering requires the grammar to "
          "generate Boolean terms only";
    throw LogicException(ss.str());
    return true;
  }
  Node basen = d_isStrong ? n : n.negate();
  NodeManager* nm = nodeManager();
  // Do i subsume the disjunction of all previous solutions? If so, we discard
  // this immediately
  Node curr;
  if (!d_curr_sols.empty())
  {
    curr = d_curr_sols.size() == 1
               ? d_curr_sols[0]
               : nm->mkNode(d_isStrong ? Kind::OR : Kind::AND, d_curr_sols);
    Node imp = nm->mkNode(Kind::AND, basen.negate(), curr);
    Trace("sygus-sol-implied")
        << "  implies: check subsumed (strong=" << d_isStrong << ") " << imp
        << "..." << std::endl;
    // check the satisfiability query
    SubsolverSetupInfo ssi(d_env, d_subOptions);
    Result r = doCheck(imp, ssi);
    Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
    if (r.getStatus() == Result::UNSAT)
    {
      // it is subsumed by the current, discard this
      return false;
    }
  }
  // check which solutions would have been filtered if the current had come
  // first
  if (options().quantifiers.sygusFilterSolRevSubsume)
  {
    std::vector<Node> nsubsume;
    for (const Node& s : d_curr_sols)
    {
      Node imp = nm->mkNode(Kind::AND, s.negate(), basen);
      Trace("sygus-sol-implied")
          << "  implies: check subsuming " << imp << "..." << std::endl;
      // check the satisfiability query
      SubsolverSetupInfo ssi(d_env, d_subOptions);
      Result r = doCheck(imp, ssi);
      Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
      if (r.getStatus() != Result::UNSAT)
      {
        nsubsume.push_back(s);
      }
      else
      {
        filtered.push_back(d_isStrong ? s : s.negate());
      }
    }
    d_curr_sols.clear();
    d_curr_sols.insert(d_curr_sols.end(), nsubsume.begin(), nsubsume.end());
  }
  d_curr_sols.push_back(basen);
  return true;
}


bool SolutionFilterStrength::addTerm(Node n, std::vector<Node>& filtered, Node conjecture)
{
  return true;
  std::cout << "Using the right one\n";
  if (!n.getType().isBoolean())
  {
    // currently, should not register non-Boolean terms here
    std::stringstream ss;
    ss << "SyGuS solution filtering requires the grammar to "
          "generate Boolean terms only";
    throw LogicException(ss.str());
    return true;
  }
  Node basen = d_isStrong ? n : n.negate();
  NodeManager* nm = nodeManager();
  // Do i subsume the disjunction of all previous solutions? If so, we discard
  // this immediately
  Node curr;
  if (!d_curr_sols.empty())
  {
    curr = d_curr_sols.size() == 1
               ? d_curr_sols[0]
               : nm->mkNode(d_isStrong ? Kind::OR : Kind::AND, d_curr_sols);
   //Node imp = nm->mkNode(Kind::AND, basen.negate(), curr);

   Node imp = nm->mkNode(Kind::AND, n, d_curr_sols[d_curr_sols.size()-1]);
   // ------------------------------------------------------------
//   TRANSFORM CONJECTURE  — USING `imp` INSTEAD OF SIDE_COND
// ------------------------------------------------------------
Node conj = conjecture;
//std::cout << "CONJ" << conj << "\n";

// conj = (and outer_forall side_cond)
//Assert(conj.getKind() == Kind::AND);
Node outer_forall = conj;     // (forall ((fpred_f B)) (not inner_forall))
AlwaysAssert(outer_forall.getKind() == Kind::FORALL);

// outer_body = (not inner_forall)
Node outer_body = outer_forall[1];
AlwaysAssert(outer_body.getKind() == Kind::NOT);

// inner_forall = (forall ((a Geometry)(b Geometry)) GEOM_BODY)
Node inner_forall = outer_body[0];
AlwaysAssert(inner_forall.getKind() == Kind::FORALL);

Node inner_bvl = inner_forall[0];    // ((a geom) (b geom))
Node aVar = inner_bvl[0];
Node bVar = inner_bvl[1];

Node geom_body = inner_forall[1];
//------------------------------------------------------------
// RECURSIVE per-application substitution: Geometry args → (aVar,bVar)
//   - resets a local counter at *each* node (so each predicate gets a fresh a/b)
//   - only maps immediate Geometry-typed children of that node
//   - traverses recursively so it reaches predicates under AND/NOT/etc.
//   - with detailed debug prints
//------------------------------------------------------------

//------------------------------------------------------------
// SUBSTITUTE GEOMETRY VARIABLES DEEP INSIDE imp
// x → aVar, y → bVar (positional per-application basis)
//------------------------------------------------------------
// std::cout << "\n[DEBUG] Original imp = " << imp << "\n";
// std::cout << "[DEBUG] Bound var aVar = " << aVar << "\n";
// std::cout << "[DEBUG] Bound var bVar = " << bVar << "\n";

NodeManager* nm = nodeManager();

// Recursive substitution function
std::function<Node(Node)> substAB = [&](Node n) -> Node {
    // Debug print for each visit
    // std::cout << "[DEBUG] Visit node: " << n << "\n";

    // Leaf → return as-is (handled positionally by parent)
    if (n.getNumChildren() == 0) {
        return n;
    }

    // For each APPLICATION node:
    // Apply positional substitution for geometry-typed *leaf* args
    std::vector<Node> newKids;
    newKids.reserve(n.getNumChildren());

    bool changed = false;

    // Reset position counter **for each application**
    int geomPos = 0;   // 0 -> aVar, 1 -> bVar, others left unchanged

    // Process all children
    for (unsigned i = 0; i < n.getNumChildren(); i++) {
        Node c = n[i];

        // Recurse first
        Node cc = substAB(c);

        if (cc != c) {
            changed = true;
            // std::cout << "    [DEBUG] Child changed by recursion:\n";
            // std::cout << "            FROM " << c << "\n";
            // std::cout << "            TO   " << cc << "\n";
        }

        // Positional substitution on *geometry-typed leaves*
        if (cc.getNumChildren() == 0 && cc.getType() == aVar.getType()) {
            // First geometry argument → aVar
            if (geomPos == 0) {
                // std::cout << "    [DEBUG] Geometry arg#" << (geomPos+1)
                //           << " " << cc << " → aVar " << aVar << "\n";
                newKids.push_back(aVar);
                changed = true;
            }
            // Second geometry argument → bVar
            else if (geomPos == 1) {
                // std::cout << "    [DEBUG] Geometry arg#" << (geomPos+1)
                //           << " " << cc << " → bVar " << bVar << "\n";
                newKids.push_back(bVar);
                changed = true;
            }
            else {
                // std::cout << "    [DEBUG] Geometry arg#" << (geomPos+1)
                //           << " EXTRA, keeping " << cc << "\n";
                newKids.push_back(cc);
            }
            geomPos++;
        }
        else {
            // Not geometry or not leaf → keep cc
            newKids.push_back(cc);
            // std::cout << "    [DEBUG] Keeping child: " << cc << "\n";
        }
    }

    // Rebuild node only if changed
    if (changed) {
        Node nn;

        // MUST use the original operator if it exists (Equals, Within, etc.)
        if (!n.getOperator().isNull()) {
            nn = nm->mkNode(n.getOperator(), newKids);
        } else {
            nn = nm->mkNode(n.getKind(), newKids);
        }

        // std::cout << "[DEBUG] Node changed:\n";
        // std::cout << "    FROM " << n << "\n";
        // std::cout << "    TO   " << nn << "\n";

        return nn;
    }

    return n;
};

// Result of deep substitution
Node imp_sub = substAB(imp);
//std::cout << "[DEBUG] Final substituted imp_sub = " << imp_sub << "\n";


//------------------------------------------------------------
// REPLACE DT_SYGUS_EVAL(...) by FALSE (not true!)
//------------------------------------------------------------
std::function<Node(Node)> stripDT = [&](Node n) -> Node {
    if (n.getKind() == Kind::DT_SYGUS_EVAL)
    {
        return nm->mkConst<bool>(false);
    }

    if (n.getNumChildren() == 0)
    {
        return n;
    }

    bool changed = false;
    std::vector<Node> newKids;
    newKids.reserve(n.getNumChildren());

    for (const Node& c : n)
    {
        Node cc = stripDT(c);
        if (cc != c) changed = true;
        newKids.push_back(cc);
    }

    if (changed)
    {
        if (!n.getOperator().isNull())
            return nm->mkNode(n.getOperator(), newKids);
        else
            return nm->mkNode(n.getKind(), newKids);
    }

    return n;
};


// ------------------------------------------------------------
//   Build inner body: (and GEOM_BODY imp_sub)
// ------------------------------------------------------------
std::cout << "OG" << conjecture << "\n";
geom_body = stripDT(geom_body);

Node negBody = geom_body;               // the OR with false at end
Node body    = nm->mkNode(Kind::NOT, negBody);

// Node not_old = nm->mkNode(Kind::NOT, old_sub);
// Node cex     = nm->mkNode(Kind::AND, Body, new_sub, not_old);

// Node exists_cex = nm->mkNode(Kind::EXISTS, bvars, cex);

Node new_inner_body = nm->mkNode(Kind::AND, body, imp_sub);

new_inner_body = nm->mkNode(Kind::NOT, new_inner_body);

//   Rebuild inner forall
Node new_inner = nm->mkNode(Kind::FORALL, inner_bvl, new_inner_body);

//   Outer negation: (not new_inner)
Node conj2 = nm->mkNode(Kind::NOT, new_inner);


std::cout << "NEQ" << conj2 << "\n";

// ------------------------------------------------------------
//   Now conj2 is your NEW CONJECTURE
// ------------------------------------------------------------
 

   // Node imp2 = nm->mkNode(Kind::AND, conjecture, imp);
   //Node imp2 = nm->mkNode(Kind::AND, conj2, imp);
    Trace("sygus-sol-implied")
        << "  implies: check subsumed (strong=" << d_isStrong << ") " << conj2
        << "..." << std::endl;
    // check the satisfiability query
    SubsolverSetupInfo ssi(d_env, d_subOptions);
    Result r = doCheck(conj2, ssi);
    Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
    if (r.getStatus() == Result::UNSAT)
    {
      // it is subsumed by the current, discard this
      return false;
    }
  }
  // check which solutions would have been filtered if the current had come
  // first
  // if (options().quantifiers.sygusFilterSolRevSubsume)
  // {
  //   std::vector<Node> nsubsume;
  //   for (const Node& s : d_curr_sols)
  //   {
  //     Node imp = nm->mkNode(Kind::AND, s.negate(), basen);
  //     Trace("sygus-sol-implied")
  //         << "  implies: check subsuming " << imp << "..." << std::endl;
  //     // check the satisfiability query
  //     SubsolverSetupInfo ssi(d_env, d_subOptions);
  //     Result r = doCheck(imp, ssi);
  //     Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
  //     if (r.getStatus() != Result::UNSAT)
  //     {
  //       nsubsume.push_back(s);
  //     }
  //     else
  //     {
  //       filtered.push_back(d_isStrong ? s : s.negate());
  //     }
  //   }
  //   d_curr_sols.clear();
  //   d_curr_sols.insert(d_curr_sols.end(), nsubsume.begin(), nsubsume.end());
  // }
  d_curr_sols.push_back(basen);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

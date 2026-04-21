/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_enumerator
 */

#include "theory/quantifiers/sygus/sygus_enumerator_callback.h"

#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/example_eval_cache.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/rewriter.h"
#include "smt/solver_engine.h"
#include "expr/dtype_cons.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusEnumeratorCallback::SygusEnumeratorCallback(Env& env,
                                                 TermDbSygus* tds,
                                                 SygusStatistics* s,
                                                 ExampleEvalCache* eec)
    : EnvObj(env), d_tds(tds), d_stats(s), d_eec(eec)
{
}




void dumpSygusGrammar(const TypeNode& tn, const std::string& name)
{
  Trace("sygus-grammar") << "==== Grammar dump: " << name << " ====\n";

  if (tn.isNull() || !tn.isDatatype())
  {
    Trace("sygus-grammar") << "  (not a datatype)\n";
    return;
  }

  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    Trace("sygus-grammar") << "  (not a sygus datatype)\n";
    return;
  }

  for (size_t i = 0, n = dt.getNumConstructors(); i < n; i++)
  {
    const DTypeConstructor& cons = dt[i];
    Node op = cons.getSygusOp();

    Trace("sygus-grammar") << "  cons[" << i << "]: ";
    if (!op.isNull())
    {
      Trace("sygus-grammar") << op;
    }
    else
    {
      Trace("sygus-grammar") << "(no op)";
    }

    Trace("sygus-grammar") << " args=(";
    for (size_t j = 0, nargs = cons.getNumArgs(); j < nargs; j++)
    {
      Trace("sygus-grammar") << cons.getArgType(j);
      if (j + 1 < nargs)
      {
        Trace("sygus-grammar") << ", ";
      }
    }
    Trace("sygus-grammar") << ")\n";
  }

  Trace("sygus-grammar") << "===============================\n";
}





bool SygusEnumeratorCallback::addTerm(const Node& n,
                                      std::unordered_set<Node>& bterms,
                                      std::unordered_set<Node>& aterms)
{
  Node bn = datatypes::utils::sygusToBuiltin(n);
  Node simp = d_env.getRewriter()->rewrite(bn);

  if (d_stats != nullptr)
  {
    ++(d_stats->d_enumTermsRewrite);
  }
  
  // Compute cache key early
  Node cval = getCacheValue(n, bn);
  Node bnRaw = datatypes::utils::sygusToBuiltin(n, /*isExternal=*/true);

//   Trace("sygus-grammar") << "Checking term: " << bnRaw << "\n";
// dumpSygusGrammar(d_blockingGrammarStn, "BLOCKING");
// dumpSygusGrammar(d_blockingGeneratorGrammarStn, "GENERATOR");


  // If we've seen it already (either accepted or blocked earlier), stop now
  if (bterms.find(cval) != bterms.end())
  {
    Trace("sygus-enum-exc-call") << "Exclude (cached): " << bnRaw << std::endl;
    return false;
  }

  // Always cache it (even if we are about to block it)
  
  
  // Now do blocking grammar pruning (but after caching)
  if (!d_blockingGrammarStn.isNull())
  {
    //  Trace("sygus-enum-exc-call-b")
    //   << "Checking bnRaw=" << bnRaw
    //   << " against blockingGrammarStn=" << d_blockingGrammarStn
    //   << " isDatatype=" << d_blockingGrammarStn.isDatatype()
    //   << " isSygusDatatype="
    //   << (d_blockingGrammarStn.isDatatype()
    //       && d_blockingGrammarStn.getDType().isSygus())
    //   << "\n";
    //   Trace("sygus-enum-exc-call-b")
    //     << "blockingGrammarStn = " << d_blockingGrammarStn << "\n";
    // if (d_blockingGrammarStn.isDatatype())
    // {
    //   const DType& dt = d_blockingGrammarStn.getDType();
    //   Trace("sygus-enum-exc-call-b")
    //       << "blockingGrammarStn numConstructors = "
    //       << dt.getNumConstructors() << "\n";
    //   for (size_t i = 0, n = dt.getNumConstructors(); i < n; i++)
    //   {
    //     Trace("sygus-enum-exc-call-b")
    //         << "  cons[" << i << "] = " << dt[i].getSygusOp() << "\n";
    //   }
    // }
    bool inbgg = datatypes::utils::isBuiltinTermInSygusGrammarDbg(d_env, bnRaw, d_blockingGeneratorGrammarStn, /*allowVars=*/true);
    if (!inbgg){
    bool inbg = datatypes::utils::isBuiltinTermInSygusGrammarDbg(d_env, bnRaw, d_blockingGrammarStn, /*allowVars=*/true);
        if (inbg)
        {
          Trace("sygus-enum-exc-call") << "Exclude (by blocking grammar): " << bnRaw << "\n";
          bterms.insert(cval);
          return false;
        }
        else {
        Trace("sygus-enum-exc-call-b") << "Blocking grammar did not exclude " << bnRaw << "\n";
        }
    } else {
      Trace("sygus-enum-exc-call-b") << "Blockig generator generated " << bnRaw << "\n";
    }
  }

  

  // callback-specific add term (examples, etc.)
  

//   for (const Node& prev : aterms)
// {
//   if (prev.getType() != bn.getType())
//   {
//     continue;
//   }
//   NodeManager* nm = nodeManager();

  // Build (not (= bn prev))
    for (const Node& prev : aterms)
  {
    if (prev.getType() != cval.getType())
    {
      continue;
    }

    NodeManager* nm = nodeManager();

    // ------------------------------------------------------------
    // Normalize both terms into the same bound-variable space.
    // ------------------------------------------------------------
    std::vector<Node> origVars;
    std::unordered_set<Node> seen;
    std::vector<Node> stack;
    stack.push_back(cval);
    stack.push_back(prev);
    if (!d_bodyAssump.isNull())
    {
      stack.push_back(d_bodyAssump);
    }

    while (!stack.empty())
    {
      Node cur = stack.back();
      stack.pop_back();

      if (cur.isVar())
      {
        if (seen.insert(cur).second)
        {
          origVars.push_back(cur);
        }
        continue;
      }
      for (const Node& c : cur)
      {
        stack.push_back(c);
      }
    }

    std::vector<Node> bvars;
    for (const Node& v : origVars)
    {
      bvars.push_back(nm->mkBoundVar(v.getType()));
    }

    Node cvalNorm = cval;
    Node prevNorm = prev;
    Node assumpNorm = d_bodyAssump;

    if (!origVars.empty())
    {
      cvalNorm = cval.substitute(origVars.begin(), origVars.end(), bvars.begin(), bvars.end());
      prevNorm = prev.substitute(origVars.begin(), origVars.end(), bvars.begin(), bvars.end());
      if (!assumpNorm.isNull())
      {
        assumpNorm =
            assumpNorm.substitute(origVars.begin(), origVars.end(), bvars.begin(), bvars.end());
      }
    }

    // ------------------------------------------------------------
    // Build "assumption ∧ (cval != prev)"
    // ------------------------------------------------------------
    Node eq = nm->mkNode(Kind::EQUAL, cvalNorm, prevNorm);
    Node diff = eq.notNode();

    Node full = diff;
    if (!assumpNorm.isNull())
    {
      full = nm->mkNode(Kind::AND, assumpNorm, diff);
    }

    Node closedQuery = full;
    if (!bvars.empty())
    {
      Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, bvars);
      closedQuery = nm->mkNode(Kind::EXISTS, bvl, full);
    }

    // ------------------------------------------------------------
    // SMT check
    // ------------------------------------------------------------
    std::unique_ptr<SolverEngine> subsolver =
        std::make_unique<SolverEngine>(nodeManager(), &options());

    subsolver->setLogic(d_env.getLogicInfo());
    subsolver->assertFormula(closedQuery);

    Result r = subsolver->checkSat();

    if (r.getStatus() == Result::UNSAT)
    {
      Trace("sygus-enum-exc-call")
          << "Exclude (by SMT equivalence under assumption): "
          << bnRaw << " == " << prev << std::endl;
      bterms.insert(cval);
      return false;
    }
  }

bterms.insert(cval);

if (!addTermInternal(n, bn, cval))
  {
    return false;
  }

// Only store if it survived SMT equivalence checks
  aterms.insert(cval);

  Trace("sygus-enum-exc-call-inc") << "Included: " << bnRaw << "\n";
  return true;
}


Node SygusEnumeratorCallback::getCacheValue(const Node& n, const Node& bn)
{
  // By default, we cache based on the rewritten form.
  // Further criteria for uniqueness (e.g. weights) may go here.
  return d_tds == nullptr ? extendedRewrite(bn) : d_tds->rewriteNode(bn);
}

bool SygusEnumeratorCallback::addTermInternal(const Node& n,
                                              const Node& bn,
                                              const Node& cval)
{
  // if we are doing PBE symmetry breaking
  Node simp = d_env.getRewriter()->rewrite(bn);
  if (d_eec != nullptr)
  {
    if (d_stats != nullptr)
    {
      ++(d_stats->d_enumTermsExampleEval);
    }
    // Is it equivalent under examples?
    // NOTE: currently assumes the cache value is the rewritten form of bn
    Assert(cval.getType() == bn.getType());
    Node bne = d_eec->addSearchVal(n.getType(), cval);
    if (!bne.isNull())
    {
      if (cval != bne)
      {
        Trace("sygus-enum-exc-call")
            << "Exclude (by examples): " << simp << ", since we already have "
            << bne << std::endl;
        return false;
      }
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

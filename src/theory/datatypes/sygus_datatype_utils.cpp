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
 * Implementation of rewriter for the theory of (co)inductive datatypes.
 */

#include "theory/datatypes/sygus_datatype_utils.h"

#include <sstream>

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/sygus_datatype.h"
#include "smt/env.h"
#include "theory/evaluator.h"
#include "theory/rewriter.h"
#include "theory/trust_substitutions.h"
#include <functional>
#include <unordered_map>
#include <unordered_set>

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {
namespace utils {

// Put this near the top of sygus_datatype_utils.cpp (same file as you showed).
// Uses Trace("sygus-bg-mem") channel for all debug output.


// ============================================================
// DEBUG: builtin-term membership in a sygus datatype grammar
// Trace channel: "sygus-bg-mem"
// ============================================================

// ============================================================
// DEBUG: builtin-term membership in a sygus datatype grammar
// Trace channel: "sygus-bg-mem"
// ============================================================

static void dbgIndent(size_t d)
{
  for (size_t i = 0; i < d; ++i) Trace("sygus-bg-mem") << "  ";
}

static void dbgPrintNode(const char* tag, const Node& n, size_t d = 0)
{
  dbgIndent(d);
  Trace("sygus-bg-mem") << tag << " = " << n << " | kind=" << n.getKind()
                        << " type=" << n.getType()
                        << " nchildren=" << n.getNumChildren()
                        << " isNull=" << n.isNull() << " isVar=" << n.isVar()
                        << " isConst=" << n.isConst() << "\n";
}

static void dbgPrintDType(const char* tag, const DType& dt, size_t d = 0)
{
  dbgIndent(d);
  Trace("sygus-bg-mem") << tag << " DType name=" << dt.getName()
                        << " isSygus=" << dt.isSygus()
                        << " sygusType="
                        << (dt.isSygus() ? dt.getSygusType() : TypeNode())
                        << " #cons=" << dt.getNumConstructors()
                        << " allowConst="
                        << (dt.isSygus() ? dt.getSygusAllowConst() : false)
                        << " allowAll="
                        << (dt.isSygus() ? dt.getSygusAllowAll() : false)
                        << "\n";
  for (size_t i = 0, n = dt.getNumConstructors(); i < n; ++i)
  {
    const DTypeConstructor& c = dt[i];
    dbgIndent(d);
    Trace("sygus-bg-mem") << "  [" << i << "] cname=" << c.getName()
                          << " nargs=" << c.getNumArgs()
                          << " weight=" << c.getWeight()
                          << " ctorNode=" << c.getConstructor()
                          << " sygusOp="
                          << (dt.isSygus() ? c.getSygusOp() : Node()) << "\n";
  }
}

// --- memo key: (TypeNode, Node) ---
struct TnNodeKey
{
  TypeNode d_tn;
  Node d_n;
  bool operator==(const TnNodeKey& o) const
  {
    return d_tn == o.d_tn && d_n == o.d_n;
  }
};

struct TnNodeKeyHash
{
  size_t operator()(const TnNodeKey& k) const
  {
    size_t h1 = std::hash<TypeNode>{}(k.d_tn);
    size_t h2 = std::hash<Node>{}(k.d_n);
    return h1 ^ (h2 + 0x9e3779b97f4a7c15ULL + (h1 << 6) + (h1 >> 2));
  }
};

// Match `templ` against `t`
// - `templ` and `t` are *builtin* terms here.
// - Only treat *hole variables* (those in `holesBuiltin`) as wildcards.
// - Any other bound variables (e.g. lambda binders) must match structurally.
static bool matchTemplateDbg(const Node& templ,
                             const Node& t,
                             const std::unordered_set<Node>& holesBuiltin,
                             std::unordered_map<Node, Node>& holeSubs,
                             size_t depth = 0)
{
  dbgIndent(depth);
  Trace("sygus-bg-mem") << "matchTemplateDbg: templ=" << templ << "  t=" << t
                        << "\n";

  // Hole?
  if (templ.getKind() == Kind::BOUND_VARIABLE)
  {
    if (holesBuiltin.find(templ) != holesBuiltin.end())
    {
      // This bound var is a hole placeholder. Enforce consistent substitution.
      auto it = holeSubs.find(templ);
      if (it == holeSubs.end())
      {
        holeSubs.emplace(templ, t);
        dbgIndent(depth);
        Trace("sygus-bg-mem") << "  HOLE bind: " << templ << " := " << t << "\n";
        return true;
      }
      bool ok = (it->second == t);
      dbgIndent(depth);
      Trace("sygus-bg-mem") << "  HOLE check: " << templ << " was " << it->second
                            << " now " << t << " -> " << ok << "\n";
      return ok;
    }
    // Not a hole: must match exactly.
    bool ok = (templ == t);
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  BOUND_VARIABLE (non-hole) exact match -> " << ok
                          << "\n";
    return ok;
  }

  // Non-hole leaf
  if (templ.getNumChildren() == 0 && t.getNumChildren() == 0)
  {
    bool ok = (templ == t);
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  LEAF exact -> " << ok << "\n";
    return ok;
  }

  // Structural checks
  if (templ.getKind() != t.getKind())
  {
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  FAIL kind mismatch\n";
    return false;
  }
  if (templ.getNumChildren() != t.getNumChildren())
  {
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  FAIL arity mismatch\n";
    return false;
  }
  // Operators must match for parameterized kinds.
  if (templ.hasOperator() || t.hasOperator())
  {
    if (!templ.hasOperator() || !t.hasOperator()
        || templ.getOperator() != t.getOperator())
    {
      dbgIndent(depth);
      Trace("sygus-bg-mem") << "  FAIL operator mismatch\n";
      return false;
    }
  }

  for (size_t i = 0, n = templ.getNumChildren(); i < n; ++i)
  {
    if (!matchTemplateDbg(templ[i], t[i], holesBuiltin, holeSubs, depth + 1))
    {
      dbgIndent(depth);
      Trace("sygus-bg-mem") << "  FAIL child " << i << "\n";
      return false;
    }
  }
  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  OK\n";
  return true;
}

// Forward decl (mutual recursion)
static bool isBuiltinInGrammarRecDbg(
    Env& env,
    const Node& t,
    const TypeNode& stn,
    bool allowVars,
    std::unordered_map<TnNodeKey, bool, TnNodeKeyHash>& memo,
    size_t depth);

// Helper: try one constructor as a template; if it matches, recurse on children.
static bool tryConstructorDbg(
    Env& env,
    const Node& t,
    const TypeNode& stn,
    size_t cindex,
    bool allowVars,
    std::unordered_map<TnNodeKey, bool, TnNodeKeyHash>& memo,
    size_t depth)
{
  const DType& gdt = stn.getDType();
  const DTypeConstructor& c = gdt[cindex];

  dbgIndent(depth);
  Trace("sygus-bg-mem") << "tryConstructorDbg: cindex=" << cindex
                        << " cname=" << c.getName()
                        << " nargs=" << c.getNumArgs()
                        << " sygusOp=" << c.getSygusOp() << "\n";

  NodeManager* nm = t.getNodeManager();

  // Nullary constructor: check if its builtin form equals `t`.
  if (c.getNumArgs() == 0)
  {
    // Build the sygus term: (APPLY_CONSTRUCTOR ctor)
    Node sz = nm->mkNode(Kind::APPLY_CONSTRUCTOR, c.getConstructor());
    Node bt = env.getRewriter()->rewrite(sygusToBuiltin(sz, /*isExternal=*/true));
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  nullary builtin=" << bt << "\n";

    bool ok = (bt == t);
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  nullary match -> " << ok << "\n";
    return ok;
  }

  // N-ary constructor: make a sygus template term with HOLE vars as children.
  std::vector<Node> args;
  args.push_back(c.getConstructor());

  // IMPORTANT FIX:
  // templB is builtin, so holes must be tracked as builtin bound vars that
  // occur in templB (i.e., sygusToBuiltin(holeS)).
  std::unordered_set<Node> holesBuiltin;

  // Map builtin-hole-var -> child nonterminal type
  std::unordered_map<Node, TypeNode> holeBuiltinToChildNt;

  for (size_t j = 0, nargs = c.getNumArgs(); j < nargs; ++j)
  {
    TypeNode childNt = c.getArgType(j);
    std::stringstream ss;
    ss << "HOLE_" << c.getName() << "_" << j;

    // Sygus-typed hole variable (bound var at sygus datatype type)
    Node holeS = NodeManager::mkBoundVar(ss.str(), childNt);
    args.push_back(holeS);

    // Builtin hole variable (what appears in templB after sygusToBuiltin + rewrite)
    Node holeB = sygusToBuiltin(holeS, /*isExternal=*/true);
    holesBuiltin.insert(holeB);
    holeBuiltinToChildNt.emplace(holeB, childNt);

    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  hole[" << j << "] sygus=" << holeS
                          << " builtin=" << holeB
                          << " childNt=" << childNt << "\n";
  }

  Node templS = nm->mkNode(Kind::APPLY_CONSTRUCTOR, args);
  Node templB = env.getRewriter()->rewrite(sygusToBuiltin(templS, /*isExternal=*/true));

  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  templS=" << templS << "\n";
  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  templB=" << templB << "\n";
  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  target t=" << t << "\n";

  std::unordered_map<Node, Node> holeSubs;  // builtinHoleVar -> matched subterm
  if (!matchTemplateDbg(templB, t, holesBuiltin, holeSubs, depth + 1))
  {
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  template did NOT match\n";
    return false;
  }

  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  template matched; checking children obligations\n";

  // For each hole substitution, recurse with the appropriate child nonterminal.
  for (const auto& kv : holeSubs)
  {
    Node holeB = kv.first;
    Node subterm = kv.second;

    auto itNt = holeBuiltinToChildNt.find(holeB);
    if (itNt == holeBuiltinToChildNt.end())
    {
      dbgIndent(depth);
      Trace("sygus-bg-mem")
          << "  WARNING: holeB not found in holeBuiltinToChildNt: " << holeB
          << "\n";
      return false;
    }

    TypeNode childNt = itNt->second;
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  recurse childNt=" << childNt
                          << " subterm=" << subterm << "\n";

    if (!isBuiltinInGrammarRecDbg(env, subterm, childNt, allowVars, memo,
                                  depth + 1))
    {
      dbgIndent(depth);
      Trace("sygus-bg-mem") << "  FAIL childNt=" << childNt << "\n";
      return false;
    }
  }

  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  SUCCESS via constructor " << c.getName() << "\n";
  return true;
}

bool isBuiltinTermInSygusGrammar(Env& env,
                                 const Node& t,
                                 const TypeNode& stn,
                                 bool allowVars)
{
  Trace("sygus-bg-mem") << "isBuiltinTermInSygusGrammar: t=" << t
                        << " kind=" << t.getKind()
                        << " type=" << t.getType()
                        << " stn=" << stn
                        << " allowVars=" << allowVars << "\n";

  if (stn.isNull() || !stn.isDatatype() || !stn.getDType().isSygus())
  {
    Trace("sygus-bg-mem") << "  top FAIL: stn not a sygus datatype\n";
    return false;
  }

  std::unordered_map<TnNodeKey, bool, TnNodeKeyHash> memo;
  return isBuiltinInGrammarRecDbg(env, t, stn, allowVars, memo, 0);
}

static bool isBuiltinInGrammarRecDbg(
    Env& env,
    const Node& t,
    const TypeNode& stn,
    bool allowVars,
    std::unordered_map<TnNodeKey, bool, TnNodeKeyHash>& memo,
    size_t depth)
{
  dbgIndent(depth);
  Trace("sygus-bg-mem") << "isBuiltinInGrammarRecDbg: stn=" << stn << " t=" << t
                        << "\n";

  if (stn.isNull() || !stn.isDatatype() || !stn.getDType().isSygus())
  {
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  FAIL: stn null/non-datatype/non-sygus\n";
    return false;
  }

  // Memo (use rewritten t to reduce churn)
  Node tr = t;
  //Node tr = env.getRewriter()->rewrite(t);
  TnNodeKey key{stn, tr};
  auto itM = memo.find(key);
  if (itM != memo.end())
  {
    dbgIndent(depth);
    Trace("sygus-bg-mem") << "  MEMO hit -> " << itM->second << "\n";
    return itM->second;
  }

  const DType& gdt = stn.getDType();
  dbgPrintDType("  grammar", gdt, depth);

  // Try each constructor as a template.
  bool ok = false;
  for (size_t i = 0, ncons = gdt.getNumConstructors(); i < ncons; ++i)
  {
    if (tryConstructorDbg(env, tr, stn, i, allowVars, memo, depth + 1))
    {
      ok = true;
      break;
    }
  }

  memo.emplace(key, ok);
  dbgIndent(depth);
  Trace("sygus-bg-mem") << "  RESULT for (stn=" << stn << ", t=" << tr
                        << ") -> " << ok << "\n";
  return ok;
}



// Public debug entrypoint.
// Put this next to the real isBuiltinTermInSygusGrammar (do not replace it).

bool isBuiltinTermInSygusGrammarDbg(Env& env,
                                    const Node& t,
                                    const TypeNode& stn,
                                    bool allowVars)
{
  Trace("sygus-bg-mem") << "====================================================\n";
  Trace("sygus-bg-mem") << "isBuiltinTermInSygusGrammarDbg\n";
  Trace("sygus-bg-mem") << "  t          = " << t << "\n";
  Trace("sygus-bg-mem") << "  t.kind     = " << t.getKind() << "\n";
  Trace("sygus-bg-mem") << "  t.type     = " << t.getType() << "\n";
  Trace("sygus-bg-mem") << "  t.isConst  = " << t.isConst() << "\n";
  Trace("sygus-bg-mem") << "  t.isVar    = " << t.isVar() << "\n";
  Trace("sygus-bg-mem") << "  t.nchild   = " << t.getNumChildren() << "\n";
  Trace("sygus-bg-mem") << "  stn        = " << stn << "\n";
  Trace("sygus-bg-mem") << "  stn.isNull = " << stn.isNull() << "\n";
  Trace("sygus-bg-mem") << "  allowVars  = " << allowVars << "\n";

  if (stn.isNull() || !stn.isDatatype())
  {
    Trace("sygus-bg-mem") << "  FAIL: stn is null or not a datatype\n";
    Trace("sygus-bg-mem") << "====================================================\n";
    return false;
  }

  const DType& gdt = stn.getDType();
  Trace("sygus-bg-mem") << "  grammar dt name=" << gdt.getName()
                        << " isSygus=" << gdt.isSygus()
                        << " #cons=" << gdt.getNumConstructors() << "\n";

  if (gdt.isSygus())
  {
    Trace("sygus-bg-mem") << "  sygus builtin type = " << gdt.getSygusType()
                          << "\n";
    Trace("sygus-bg-mem") << "  allowConst=" << gdt.getSygusAllowConst()
                          << " allowAll=" << gdt.getSygusAllowAll() << "\n";
    Node vlist = gdt.getSygusVarList();
    Trace("sygus-bg-mem") << "  varList = " << vlist << "\n";
  }
  Node tr = t;
  //Node tr = env.getRewriter()->rewrite(t);
  Trace("sygus-bg-mem") << "  rewrite(t) = " << tr << "\n";

  bool r0 = isBuiltinTermInSygusGrammar(env, t, stn, allowVars);
  bool r1 = (tr == t) ? r0 : isBuiltinTermInSygusGrammar(env, tr, stn, allowVars);

  Trace("sygus-bg-mem") << "  isBuiltinTermInSygusGrammar(t)  = " << r0 << "\n";
  Trace("sygus-bg-mem") << "  isBuiltinTermInSygusGrammar(rt) = " << r1 << "\n";

  bool ret = r1;

  Trace("sygus-bg-mem") << "  ==> returning " << ret << "\n";
  Trace("sygus-bg-mem") << "====================================================\n";
  return ret;
}


Node applySygusArgs(const DType& dt,
                    Node op,
                    Node n,
                    const std::vector<Node>& args)
{
  // optimization: if n is just a sygus bound variable, return immediately
  // by replacing with the proper argument, or returning unchanged if it is
  // a bound variable not corresponding to a formal argument.
  if (n.getKind() == Kind::BOUND_VARIABLE)
  {
    if (n.hasAttribute(SygusVarNumAttribute()))
    {
      int vn = n.getAttribute(SygusVarNumAttribute());
      Assert(dt.getSygusVarList()[vn] == n);
      return args[vn];
    }
    // it is a different bound variable, it is unchanged
    return n;
  }
  // n is an application of operator op.
  // We must compute the free variables in op to determine if there are
  // any substitutions we need to make to n.
  TNode val;
  if (!op.hasAttribute(SygusVarFreeAttribute()))
  {
    std::unordered_set<Node> fvs;
    if (expr::getFreeVariables(op, fvs))
    {
      if (fvs.size() == 1)
      {
        for (const Node& v : fvs)
        {
          val = v;
        }
      }
      else
      {
        val = op;
      }
    }
    Trace("dt-sygus-fv") << "Free var in " << op << " : " << val << std::endl;
    op.setAttribute(SygusVarFreeAttribute(), val);
  }
  else
  {
    val = op.getAttribute(SygusVarFreeAttribute());
  }
  if (val.isNull())
  {
    return n;
  }
  if (val.getKind() == Kind::BOUND_VARIABLE)
  {
    // single substitution case
    int vn = val.getAttribute(SygusVarNumAttribute());
    TNode sub = args[vn];
    return n.substitute(val, sub);
  }
  // do the full substitution
  std::vector<Node> vars;
  Node bvl = dt.getSygusVarList();
  for (unsigned i = 0, nvars = bvl.getNumChildren(); i < nvars; i++)
  {
    vars.push_back(bvl[i]);
  }
  return n.substitute(vars.begin(), vars.end(), args.begin(), args.end());
}

Kind getOperatorKindForSygusBuiltin(Node op)
{
  Assert(op.getKind() != Kind::BUILTIN);
  if (op.getKind() == Kind::LAMBDA)
  {
    return Kind::APPLY_UF;
  }
  return NodeManager::getKindForFunction(op);
}

Node mkSygusTerm(const DType& dt,
                 unsigned i,
                 const std::vector<Node>& children,
                 bool doBetaReduction,
                 bool isExternal)
{
  Trace("dt-sygus-util") << "Make sygus term " << dt.getName() << "[" << i
                         << "] with children: " << children << std::endl;
  Assert(i < dt.getNumConstructors());
  Assert(dt.isSygus());
  Assert(!dt[i].getSygusOp().isNull());
  Node op = dt[i].getSygusOp();
  Node opn = op;
  if (!isExternal)
  {
    // Get the normalized version of the sygus operator. We do this by
    // expanding definitions.
    if (!op.isConst())
    {
      // Get the expanded definition form, if it has been marked. This ensures
      // that user-defined functions have been eliminated from op.
      opn = getExpandedDefinitionForm(op);
    }
  }
  // if it is the any constant, we simply return the child
  if (dt[i].isSygusAnyConstant())
  {
    Assert(children.size() == 1);
    return children[0];
  }
  Node ret = mkSygusTerm(opn, children, doBetaReduction);
  Assert(ret.getType() == dt.getSygusType());
  return ret;
}

Node mkSygusTerm(const Node& op,
                 const std::vector<Node>& children,
                 bool doBetaReduction)
{
  NodeManager* nm = op.getNodeManager();
  Assert(op.getInternalSkolemId() != InternalSkolemId::SYGUS_ANY_CONSTANT);
  Trace("dt-sygus-util") << "Operator is " << op << std::endl;
  if (children.empty())
  {
    // no children, return immediately
    Trace("dt-sygus-util") << "...return direct op" << std::endl;
    return op;
  }
  std::vector<Node> schildren;
  // get the kind of the operator
  Kind ok = op.getKind();
  if (ok != Kind::BUILTIN)
  {
    if (ok == Kind::LAMBDA && doBetaReduction)
    {
      // Do immediate beta reduction. It suffices to use a normal substitution
      // since neither op nor children have quantifiers, since they are
      // generated by sygus grammars.
      std::vector<Node> vars{op[0].begin(), op[0].end()};
      Assert(vars.size() == children.size());
      Node ret = op[1].substitute(
          vars.begin(), vars.end(), children.begin(), children.end());
      Trace("dt-sygus-util") << "...return (beta-reduce) " << ret << std::endl;
      return ret;
    }
    else
    {
      schildren.push_back(op);
    }
  }
  schildren.insert(schildren.end(), children.begin(), children.end());
  Node ret;
  if (ok == Kind::BUILTIN)
  {
    ret = nm->mkNode(op, schildren);
    Trace("dt-sygus-util") << "...return (builtin) " << ret << std::endl;
    return ret;
  }
  // get the kind used for applying op
  Kind otk = NodeManager::operatorToKind(op);
  Trace("dt-sygus-util") << "operator kind is " << otk << std::endl;
  if (otk != Kind::UNDEFINED_KIND)
  {
    // If it is an APPLY_UF operator, we should have at least an operator and
    // a child.
    Assert(otk != Kind::APPLY_UF || schildren.size() != 1);
    ret = nm->mkNode(otk, schildren);
    Trace("dt-sygus-util") << "...return (op) " << ret << std::endl;
    return ret;
  }
  Kind tok = getOperatorKindForSygusBuiltin(op);
  if (schildren.size() == 1 && tok == Kind::UNDEFINED_KIND)
  {
    ret = schildren[0];
  }
  else
  {
    ret = nm->mkNode(tok, schildren);
  }
  Trace("dt-sygus-util") << "...return " << ret << std::endl;
  return ret;
}

struct SygusToBuiltinTermAttributeId
{
};
typedef expr::Attribute<SygusToBuiltinTermAttributeId, Node>
    SygusToBuiltinTermAttribute;

// A variant of the above attribute for cases where we introduce a fresh
// variable. This is to support sygusToBuiltin on non-constant sygus terms,
// where sygus variables should be mapped to canonical builtin variables.
// It is important to cache this so that sygusToBuiltin is deterministic.
struct SygusToBuiltinVarAttributeId
{
};
typedef expr::Attribute<SygusToBuiltinVarAttributeId, Node>
    SygusToBuiltinVarAttribute;

// A variant of the above attribute for cases where we introduce a fresh
// variable. This is to support sygusToBuiltin on non-constant sygus terms,
// where sygus variables should be mapped to canonical builtin variables.
// It is important to cache this so that sygusToBuiltin is deterministic.
struct BuiltinVarToSygusAttributeId
{
};
typedef expr::Attribute<BuiltinVarToSygusAttributeId, Node>
    BuiltinVarToSygusAttribute;

Node sygusToBuiltin(Node n, bool isExternal)
{
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  unsigned index;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // Notice this condition succeeds in roughly 99% of the executions of this
      // method (based on our coverage tests), hence the else if / else cases
      // below do not significantly impact performance.
      if (cur.getKind() == Kind::APPLY_CONSTRUCTOR)
      {
        if (!isExternal && cur.hasAttribute(SygusToBuiltinTermAttribute()))
        {
          visited[cur] = cur.getAttribute(SygusToBuiltinTermAttribute());
        }
        else
        {
          visited[cur] = Node::null();
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
      }
      else if (cur.getType().isSygusDatatype())
      {
        Assert (cur.isVar());
        if (cur.hasAttribute(SygusToBuiltinVarAttribute()))
        {
          // use the previously constructed variable for it
          visited[cur] = cur.getAttribute(SygusToBuiltinVarAttribute());
        }
        else
        {
          std::stringstream ss;
          ss << cur;
          const DType& dt = cur.getType().getDType();
          // make a fresh variable
          Node var = NodeManager::mkBoundVar(ss.str(), dt.getSygusType());
          SygusToBuiltinVarAttribute stbv;
          cur.setAttribute(stbv, var);
          visited[cur] = var;
          // create backwards mapping
          BuiltinVarToSygusAttribute bvtsa;
          var.setAttribute(bvtsa, cur);
        }
      }
      else
      {
        // non-datatypes are themselves
        visited[cur] = cur;
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      Assert(cur.getKind() == Kind::APPLY_CONSTRUCTOR);
      const DType& dt = cur.getType().getDType();
      // Non sygus-datatype terms are also themselves. Notice we treat the
      // case of non-sygus datatypes this way since it avoids computing
      // the type / datatype of the node in the pre-traversal above. The
      // case of non-sygus datatypes is very rare, so the extra addition to
      // visited is justified performance-wise.
      if (dt.isSygus())
      {
        std::vector<Node> children;
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          children.push_back(it->second);
        }
        index = indexOf(cur.getOperator());
        ret = mkSygusTerm(dt, index, children, true, isExternal);
      }
      visited[cur] = ret;
      // cache
      if (!isExternal)
      {
        SygusToBuiltinTermAttribute stbt;
        cur.setAttribute(stbt, ret);
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node builtinVarToSygus(Node v)
{
  BuiltinVarToSygusAttribute bvtsa;
  if (v.hasAttribute(bvtsa))
  {
    return v.getAttribute(bvtsa);
  }
  return Node::null();
}

/**
 * Get free symbols or variables in a sygus datatype type.
 * @param sdt The sygus datatype.
 * @param sym The symbols to add to.
 * @param isVar If we are looking for variables (if not, we are looking for
 * symbols).
 */
void getFreeSymbolsSygusTypeInternal(TypeNode sdt,
                                     std::unordered_set<Node>& syms,
                                     bool isVar)
{
  // datatype types we need to process
  std::vector<TypeNode> typeToProcess;
  // datatype types we have processed
  std::unordered_set<TypeNode> typesProcessed;
  typeToProcess.push_back(sdt);
  while (!typeToProcess.empty())
  {
    std::vector<TypeNode> typeNextToProcess;
    for (const TypeNode& curr : typeToProcess)
    {
      Assert(curr.isDatatype() && curr.getDType().isSygus());
      const DType& dtc = curr.getDType();
      for (unsigned j = 0, ncons = dtc.getNumConstructors(); j < ncons; j++)
      {
        // collect the symbols from the operator
        Node op = dtc[j].getSygusOp();
        if (isVar)
        {
          expr::getVariables(op, syms);
        }
        else
        {
          expr::getSymbols(op, syms);
        }
        // traverse the argument types
        for (unsigned k = 0, nargs = dtc[j].getNumArgs(); k < nargs; k++)
        {
          TypeNode argt = dtc[j].getArgType(k);
          if (!argt.isDatatype() || !argt.getDType().isSygus())
          {
            // not a sygus datatype
            continue;
          }
          if (typesProcessed.find(argt) == typesProcessed.end())
          {
            typesProcessed.insert(argt);
            typeNextToProcess.push_back(argt);
          }
        }
      }
    }
    typeToProcess.clear();
    typeToProcess.insert(typeToProcess.end(),
                         typeNextToProcess.begin(),
                         typeNextToProcess.end());
  }
}

void getFreeSymbolsSygusType(TypeNode sdt, std::unordered_set<Node>& syms)
{
  getFreeSymbolsSygusTypeInternal(sdt, syms, false);
}

void getFreeVariablesSygusType(TypeNode sdt, std::unordered_set<Node>& syms)
{
  getFreeSymbolsSygusTypeInternal(sdt, syms, true);
}

TypeNode substituteAndGeneralizeSygusType(TypeNode sdt,
                                          const std::vector<Node>& syms,
                                          const std::vector<Node>& vars)
{
  NodeManager* nm = sdt.getNodeManager();
  const DType& sdtd = sdt.getDType();
  // compute the new formal argument list
  std::vector<Node> formalVars;
  Node prevVarList = sdtd.getSygusVarList();
  if (!prevVarList.isNull())
  {
    for (const Node& v : prevVarList)
    {
      // if it is not being replaced
      if (std::find(syms.begin(), syms.end(), v) != syms.end())
      {
        formalVars.push_back(v);
      }
    }
  }
  for (const Node& v : vars)
  {
    if (v.getKind() == Kind::BOUND_VARIABLE)
    {
      formalVars.push_back(v);
    }
  }
  // make the sygus variable list for the formal argument list
  Node abvl;
  if (!formalVars.empty())
  {
    abvl = nm->mkNode(Kind::BOUND_VAR_LIST, formalVars);
  }
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  // must convert all constructors to version with variables in "vars"
  std::vector<SygusDatatype> sdts;

  Trace("dtsygus-gen-debug") << "Process sygus type:" << std::endl;
  Trace("dtsygus-gen-debug") << sdtd.getName() << std::endl;

  // datatype types we need to process
  std::vector<TypeNode> dtToProcess;
  // datatype types we have processed
  std::map<TypeNode, TypeNode> dtProcessed;
  dtToProcess.push_back(sdt);
  std::stringstream ssutn0;
  ssutn0 << sdtd.getName() << "_s";
  TypeNode abdTNew = nm->mkUnresolvedDatatypeSort(ssutn0.str());
  dtProcessed[sdt] = abdTNew;

  // We must convert all symbols in the sygus datatype type sdt to
  // apply the substitution { syms -> vars }, where syms is the free
  // variables of the input problem, and vars is the formal argument list
  // of the function-to-synthesize.

  // We are traversing over the subfield types of the datatype to convert
  // them into the form described above.
  while (!dtToProcess.empty())
  {
    std::vector<TypeNode> dtNextToProcess;
    for (const TypeNode& curr : dtToProcess)
    {
      Assert(curr.isDatatype() && curr.getDType().isSygus());
      const DType& dtc = curr.getDType();
      std::stringstream ssdtn;
      ssdtn << dtc.getName() << "_s";
      sdts.push_back(SygusDatatype(ssdtn.str()));
      Trace("dtsygus-gen-debug")
          << "Process datatype " << sdts.back().getName() << "..." << std::endl;
      for (unsigned j = 0, ncons = dtc.getNumConstructors(); j < ncons; j++)
      {
        // if the any constant constructor, we just carry it to the new datatype
        if (dtc[j].isSygusAnyConstant())
        {
          sdts.back().addAnyConstantConstructor(dtc[j].getArgType(0));
          continue;
        }
        Node op = dtc[j].getSygusOp();
        // apply the substitution to the argument
        Node ops =
            op.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
        Trace("dtsygus-gen-debug") << "  Process constructor " << op << " / "
                                   << ops << "..." << std::endl;
        std::vector<TypeNode> cargs;
        for (unsigned k = 0, nargs = dtc[j].getNumArgs(); k < nargs; k++)
        {
          TypeNode argt = dtc[j].getArgType(k);
          TypeNode argtNew;
          if (argt.isDatatype() && argt.getDType().isSygus())
          {
            std::map<TypeNode, TypeNode>::iterator itdp =
                dtProcessed.find(argt);
            if (itdp == dtProcessed.end())
            {
              std::stringstream ssutn;
              ssutn << argt.getDType().getName() << "_s";
              argtNew = nm->mkUnresolvedDatatypeSort(ssutn.str());
              Trace("dtsygus-gen-debug") << "    ...unresolved type " << argtNew
                                         << " for " << argt << std::endl;
              dtProcessed[argt] = argtNew;
              dtNextToProcess.push_back(argt);
            }
            else
            {
              argtNew = itdp->second;
            }
          }
          else
          {
            argtNew = argt;
          }
          Trace("dtsygus-gen-debug")
              << "    Arg #" << k << ": " << argtNew << std::endl;
          cargs.push_back(argtNew);
        }
        std::stringstream ss;
        ss << ops.getKind();
        Trace("dtsygus-gen-debug") << "Add constructor : " << ops << std::endl;
        sdts.back().addConstructor(ops, ss.str(), cargs);
      }
      Trace("dtsygus-gen-debug")
          << "Set sygus : " << dtc.getSygusType() << " " << abvl << std::endl;
      TypeNode stn = dtc.getSygusType();
      sdts.back().initializeDatatype(
          stn, abvl, dtc.getSygusAllowConst(), dtc.getSygusAllowAll());
    }
    dtToProcess.clear();
    dtToProcess.insert(
        dtToProcess.end(), dtNextToProcess.begin(), dtNextToProcess.end());
  }
  Trace("dtsygus-gen-debug")
      << "Make " << sdts.size() << " datatype types..." << std::endl;
  // extract the datatypes
  std::vector<DType> datatypes;
  for (unsigned i = 0, ndts = sdts.size(); i < ndts; i++)
  {
    datatypes.push_back(sdts[i].getDatatype());
  }
  // make the datatype types
  std::vector<TypeNode> datatypeTypes = nm->mkMutualDatatypeTypes(datatypes);
  TypeNode sdtS = datatypeTypes[0];
  if (TraceIsOn("dtsygus-gen-debug"))
  {
    Trace("dtsygus-gen-debug") << "Made datatype types:" << std::endl;
    for (unsigned j = 0, ndts = datatypeTypes.size(); j < ndts; j++)
    {
      const DType& dtj = datatypeTypes[j].getDType();
      Trace("dtsygus-gen-debug") << "#" << j << ": " << dtj << std::endl;
    }
  }
  return sdtS;
}

TypeNode generalizeSygusType(TypeNode sdt)
{
  std::unordered_set<Node> syms;
  getFreeSymbolsSygusType(sdt, syms);
  if (syms.empty())
  {
    return sdt;
  }
  std::vector<Node> svec;
  std::vector<Node> vars;
  for (const Node& s : syms)
  {
    svec.push_back(s);
    vars.push_back(NodeManager::mkBoundVar(s.getName(), s.getType()));
  }
  return substituteAndGeneralizeSygusType(sdt, svec, vars);
}

unsigned getSygusTermSize(Node n)
{
  if (n.getKind() != Kind::APPLY_CONSTRUCTOR)
  {
    return 0;
  }
  unsigned sum = 0;
  for (const Node& nc : n)
  {
    sum += getSygusTermSize(nc);
  }
  const DType& dt = datatypeOf(n.getOperator());
  int cindex = indexOf(n.getOperator());
  Assert(cindex >= 0 && static_cast<size_t>(cindex) < dt.getNumConstructors());
  unsigned weight = dt[cindex].getWeight();
  return weight + sum;
}

/**
 * Map terms to the result of expand definitions calling smt::expandDefinitions
 * on it.
 */
struct SygusExpDefFormAttributeId
{
};
typedef expr::Attribute<SygusExpDefFormAttributeId, Node>
    SygusExpDefFormAttribute;

void setExpandedDefinitionForm(Node op, Node eop)
{
  op.setAttribute(SygusExpDefFormAttribute(), eop);
}

Node getExpandedDefinitionForm(Node op)
{
  Node eop = op.getAttribute(SygusExpDefFormAttribute());
  // if not set, assume original
  return eop.isNull() ? op : eop;
}

void computeExpandedDefinitionForms(Env& env, const TypeNode& tn)
{
  std::unordered_set<TypeNode> processed;
  std::vector<TypeNode> toProcess;
  toProcess.push_back(tn);
  while (!toProcess.empty())
  {
    TypeNode tnp = toProcess.back();
    toProcess.pop_back();
    Assert(tnp.isSygusDatatype());
    const DType& dt = tnp.getDType();
    const std::vector<std::shared_ptr<DTypeConstructor>>& cons =
        dt.getConstructors();
    for (const std::shared_ptr<DTypeConstructor>& c : cons)
    {
      Node op = c->getSygusOp();
      Node eop = env.getTopLevelSubstitutions().apply(op);
      eop = env.getRewriter()->rewrite(eop);
      setExpandedDefinitionForm(op, eop);
      // also must consider the arguments
      for (size_t j = 0, nargs = c->getNumArgs(); j < nargs; ++j)
      {
        TypeNode tnc = c->getArgType(j);
        if (tnc.isSygusDatatype() && processed.find(tnc) == processed.end())
        {
          toProcess.push_back(tnc);
          processed.insert(tnc);
        }
      }
    }
  }
}

}  // namespace utils
}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

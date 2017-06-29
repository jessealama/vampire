/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"

#include "Indexing/TermSharing.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "KBO.hpp"
#include "Signature.hpp"

#include <fstream>


#define NONINTERPRETED_PRECEDENCE_BOOST 0x1000

#define NONINTERPRETED_LEVEL_BOOST 0x1000
#define COLORED_WEIGHT_BOOST 0x10000
#define COLORED_LEVEL_BOOST 0x10000

#include <sstream>

namespace Kernel {

using namespace Lib;
using namespace Shell;


/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO::State
{
public:
  /** Initialise the state */
  State(KBO* kbo)
    : _kbo(*kbo)
  {}

  void init()
  {
    _weightDiff=0;
    _posNum=0;
    _negNum=0;
    _lexResult=EQUAL;
    _varDiffs.reset();
  }

  CLASS_NAME(KBO::State);
  USE_ALLOCATOR(State);

  void traverse(Term* t1, Term* t2);
  void traverse(TermList tl,int coefficient);
  Result result(Term* t1, Term* t2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(TermList t1, TermList t2);
  Result applyVariableCondition(Result res)
  {
    if(_posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    } else if(_negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    }
    return res;
  }

  int _weightDiff;
  DHMap<unsigned, int, IdentityHash> _varDiffs;
  /** Number of variables, that occur more times in the first literal */
  int _posNum;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** First comparison result */
  Result _lexResult;
  /** The ordering used */
  KBO& _kbo;
  /** The variable counters */
}; // class KBO::State

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result KBO::State::result(Term* t1, Term* t2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(t1->functor()!=t2->functor()) {
    if(t1->isLiteral()) {
      int prec1, prec2;
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    } else {
      res=_kbo.compareFunctionPrecedences(t1->functor(), t2->functor());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);

  //the result should never be EQUAL:
  //- either t1 and t2 are truely equal. But then if they're equal, it
  //would have been discovered by the t1==t2 check in
  //KBO::compare methods.
  //- or literals t1 and t2 are equal but for their polarity. But such
  //literals should never occur in a clause that would exist long enough
  //to get to ordering --- it should be deleted by tautology deletion.
  ASS_NEQ(res, EQUAL);
  return res;
}

Ordering::Result KBO::State::innerResult(TermList tl1, TermList tl2)
{
  CALL("KBO::State::innerResult");

  ASS_NEQ(tl1, tl2);
  ASS(!TermList::sameTopFunctor(tl1,tl2));

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(tl1.isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(tl2.isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else {
      res=_kbo.compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

void KBO::State::recordVariable(unsigned var, int coef)
{
  CALL("KBO::State::recordVariable");
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    } else if(*pnum==1) {
      _posNum++;
    }
  } else {
    if(*pnum==0) {
      _posNum--;
    } else if(*pnum==-1) {
      _negNum++;
    }
  }
}

void KBO::State::traverse(TermList tl,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(tl.isOrdinaryVar()) {
    _weightDiff+=_kbo._variableWeight*coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  _weightDiff+=_kbo.functionSymbolWeight(t->functor())*coef;

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      _weightDiff+=_kbo.functionSymbolWeight(ts->term()->functor())*coef;
      if(ts->term()->arity()) {
	stack.push(ts->term()->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      _weightDiff+=_kbo._variableWeight*coef;
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void KBO::State::traverse(Term* t1, Term* t2)
{
  CALL("KBO::State::traverse");
  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<TermList*> stack(32);
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!stack.isEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      depth--;
      ASS_NEQ(_lexResult,EQUAL);
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
	lexValidDepth=depth;
	if(_weightDiff!=0) {
	  _lexResult=_weightDiff>0 ? GREATER : LESS;
	}
	_lexResult=applyVariableCondition(_lexResult);
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      ASS(ss->term()->arity());
      stack.push(ss->term()->args());
      stack.push(tt->term()->args());
      depth++;
    } else {
      traverse(*ss,1);
      traverse(*tt,-1);
      if(_lexResult==EQUAL) {
	_lexResult=innerResult(*ss, *tt);
	lexValidDepth=depth;
	ASS(_lexResult!=EQUAL);
	ASS(_lexResult!=GREATER_EQ);
	ASS(_lexResult!=LESS_EQ);
      }
    }
  }
  ASS_EQ(depth,0);
}


/**
 * Create a KBO object.
 */
KBO::KBO(Problem& prb, const Options& opt)
 : KBOBase(prb, opt)
{
  CALL("KBO::KBO");

  _variableWeight = 1;
  _defaultSymbolWeight = 1;

  _state=new State(this);
}

KBO::~KBO()
{
  CALL("KBO::~KBO");

  delete _state;
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::compare(Literal* l1, Literal* l2) const
{
  CALL("KBO::compare(Literal*...)");
  ASS(l1->shared());
  ASS(l2->shared());

  if (l1 == l2) {
    return EQUAL;
  }

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if( (l1->isNegative() ^ l2->isNegative()) && (p1==p2) &&
	  l1->weight()==l2->weight() && l1->vars()==l2->vars() &&  //this line is just optimization, so we don't check whether literals are opposite when they cannot be
	  l1==env.sharing->tryGetOpposite(l2)) {
    return l1->isNegative() ? LESS : GREATER;
  }

  Result res;

  if (p1 != p2) {
    int lev1 = predicateLevel(p1);
    int lev2 = predicateLevel(p2);
    if (lev1 > lev2) {
      res=GREATER;
      goto fin;
    }
    if (lev2 > lev1) {
      res=LESS;
      goto fin;
    }
  }

  if(l1->isEquality()) {
    ASS(l2->isEquality());
    return compareEqualities(l1, l2);
  }
  ASS(!l1->isEquality());

  {
    ASS(_state);
    State* state=_state;
#if VDEBUG
    //this is to make sure _state isn't used while we're using it
    _state=0;
#endif
    state->init();
    if(p1!=p2) {
      TermList* ts;
      ts=l1->args();
      while(!ts->isEmpty()) {
	state->traverse(*ts,1);
	ts=ts->next();
      }
      ts=l2->args();
      while(!ts->isEmpty()) {
	state->traverse(*ts,-1);
	ts=ts->next();
      }
    } else {
      state->traverse(l1,l2);
    }

    res=state->result(l1,l2);
#if VDEBUG
    _state=state;
#endif
  }

fin:
  if(_reverseLCM && (l1->isNegative() || l2->isNegative()) ) {
    if(l1->isNegative() && l2->isNegative()) {
      res = reverse(res);
    }
    else {
      res = l1->isNegative() ? LESS : GREATER;
    }
  }
  return res;
} // KBO::compare()

Ordering::Result KBO::compare(TermList tl1, TermList tl2) const
{
  CALL("KBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
    }
  }
  if(tl2.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
    }
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif

  state->init();
  if(t1->functor()==t2->functor()) {
    state->traverse(t1,t2);
  } else {
    state->traverse(tl1,1);
    state->traverse(tl2,-1);
  }
  Result res=state->result(t1,t2);
#if VDEBUG
  _state=state;
#endif
  return res;
}

int KBO::functionSymbolWeight(unsigned fun) const
{
  int weight = _defaultSymbolWeight;

  if(env.signature->functionColored(fun)) {
    weight *= COLORED_WEIGHT_BOOST;
  }

  return weight;
}

//////////////////////////////////////////////////
// KBOBase class
//////////////////////////////////////////////////

/**
 * Return the predicate level. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality). If a predicate is colored, its level is multiplied by
 * the COLORED_LEVEL_BOOST value.
 * @since 11/05/2008 Manchester
 */
int KBOBase::predicateLevel (unsigned pred) const
{
  int basic=pred >= _predicates ? 1 : _predicateLevels[pred];
  if(NONINTERPRETED_LEVEL_BOOST && !env.signature->getPredicate(pred)->interpreted()) {
    ASS_NEQ(pred,0); //equality is always interpreted
    basic+=NONINTERPRETED_LEVEL_BOOST;
  }
  if(env.signature->predicateColored(pred)) {
    ASS_NEQ(pred,0); //equality should never be colored
    return COLORED_LEVEL_BOOST*basic;
  } else {
    return basic;
  }
} // KBO::predicateLevel


/**
 * Return the predicate precedence. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicatePrecedences,
 * otherwise it is defined to be @b pred (to make it greater than all
 * previously introduced predicates).
 * @since 11/05/2008 Manchester
 */
int KBOBase::predicatePrecedence (unsigned pred) const
{
  int res=pred >= _predicates ? (int)pred : _predicatePrecedences[pred];
  if(NONINTERPRETED_PRECEDENCE_BOOST) {
    ASS_EQ(NONINTERPRETED_PRECEDENCE_BOOST & 1, 0); // an even number

    bool intp = env.signature->getPredicate(pred)->interpreted();
    res *= 2;
    return intp ? res+1 : res+NONINTERPRETED_PRECEDENCE_BOOST;
  }
  return res;
} // KBO::predicatePrecedences

Comparison KBOBase::compareFunctors(unsigned fun1, unsigned fun2) const
{
  CALL("KBOBase::compareFunctors");

  if(fun1==fun2) {
    return Lib::EQUAL;
  }
  switch(compareFunctionPrecedences(fun1, fun2)) {
  case GREATER: return Lib::GREATER;
  case LESS: return Lib::LESS;
  default:
    ASSERTION_VIOLATION;
  }
}

/**
 * Compare precedences of two function symbols
 */
Ordering::Result KBOBase::compareFunctionPrecedences(unsigned fun1, unsigned fun2) const
{
  CALL("KBOBase::compareFunctionPrecedences");
  ASS_NEQ(fun1, fun2);

  // $$false is the smallest
  if (env.signature->isFoolConstantSymbol(false,fun1)) {
    return LESS;
  }
  if (env.signature->isFoolConstantSymbol(false,fun2)) {
    return GREATER;
  }

  // $$true is the second smallest
  if (env.signature->isFoolConstantSymbol(true,fun1)) {
    return LESS;
  }

  if (env.signature->isFoolConstantSymbol(true,fun2)) {
    return GREATER;
  }

  Signature::Symbol* s1=env.signature->getFunction(fun1);
  Signature::Symbol* s2=env.signature->getFunction(fun2);
  // uninterpreted things are greater than interpreted things
  if(!s1->interpreted()) {
    if(s2->interpreted()) {
      return GREATER;
    }
    //two non-interpreted functions
    return fromComparison(Int::compare(
        fun1 >= _functions ? (int)fun1 : _functionPrecedences[fun1],
        fun2 >= _functions ? (int)fun2 : _functionPrecedences[fun2] ));
  }
  if(!s2->interpreted()) {
    return LESS;
  }
  if(s1->arity()) {
    if(!s2->arity()) {
      return GREATER;
    }
    //two interpreted functions
    return fromComparison(Int::compare(fun1, fun2));
  }
  if(s2->arity()) {
    return LESS;
  }
  //two interpreted constants

  if (!s1->numericConstant() || !s2->numericConstant()) {
    return fromComparison(Int::compare(fun1, fun2));
  }

  Comparison cmpRes;
  if(s1->integerConstant() && s2->integerConstant()) {
    cmpRes = IntegerConstantType::comparePrecedence(s1->integerValue(), s2->integerValue());
  }
  else if(s1->rationalConstant() && s2->rationalConstant()) {
    cmpRes = RationalConstantType::comparePrecedence(s1->rationalValue(), s2->rationalValue());
  }
  else if(s1->realConstant() && s2->realConstant()) {
    cmpRes = RealConstantType::comparePrecedence(s1->realValue(), s2->realValue());
  }
  else if(s1->integerConstant()) {
    ASS_REP(s2->rationalConstant() || s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->integerConstant()) {
    ASS_REP(s1->rationalConstant() || s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else if(s1->rationalConstant()) {
    ASS_REP(s2->realConstant(), s2->name());
    cmpRes = Lib::LESS;
  }
  else if(s2->rationalConstant()) {
    ASS_REP(s1->realConstant(), s1->name());
    cmpRes = Lib::GREATER;
  }
  else {
    ASSERTION_VIOLATION;
    cmpRes = Int::compare(fun1, fun2);
  }
  return fromComparison(cmpRes);
}

/*
template<typename Comparator>
struct FnBoostWrapper
{
  FnBoostWrapper(Comparator comp) : _comp(comp) {}
  Comparator _comp;

  Comparison compare(unsigned f1, unsigned f2)
  {
    static Options::SymbolPrecedenceBoost boost = env.options->symbolPrecedenceBoost();
    Comparison res = EQUAL;
    bool u1 = env.signature->getFunction(f1)->inUnit(); 
    bool u2 = env.signature->getFunction(f2)->inUnit(); 
    bool g1 = env.signature->getFunction(f1)->inGoal();
    bool g2 = env.signature->getFunction(f2)->inGoal();
    switch(boost){
      case Options::SymbolPrecedenceBoost::NONE:
        break;
      case Options::SymbolPrecedenceBoost::GOAL:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::UNIT:
        if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::GOAL_UNIT:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        else if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
    }
    if(res==EQUAL){
      res = _comp.compare(f1,f2);
    }
    return res;
  }

};
template<typename Comparator>
struct PredBoostWrapper
{
  PredBoostWrapper(Comparator comp) : _comp(comp) {}
  Comparator _comp;

  Comparison compare(unsigned p1, unsigned p2)
  {
    static Options::SymbolPrecedenceBoost boost = env.options->symbolPrecedenceBoost();
    Comparison res = EQUAL;
    bool u1 = env.signature->getPredicate(p1)->inUnit();
    bool u2 = env.signature->getPredicate(p2)->inUnit();
    bool g1 = env.signature->getPredicate(p1)->inGoal();
    bool g2 = env.signature->getPredicate(p2)->inGoal();
    switch(boost){
      case Options::SymbolPrecedenceBoost::NONE:
        break;
      case Options::SymbolPrecedenceBoost::GOAL:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::UNIT:
        if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
      case Options::SymbolPrecedenceBoost::GOAL_UNIT:
        if(g1 && !g2){ res = GREATER; }
        else if(!g1 && g2){ res = LESS; }
        else if(u1 && !u2){ res = GREATER; }
        else if(!u1 && u2){ res = LESS; }
        break;
    }
    if(res==EQUAL){
      res = _comp.compare(p1,p2);
    }
    return res;
  }
};

struct FnFreqComparator
{
  Comparison compare(unsigned f1, unsigned f2)
  {
    unsigned c1 = env.signature->getFunction(f1)->usageCnt();
    unsigned c2 = env.signature->getFunction(f2)->usageCnt();
    Comparison res = Int::compare(c2,c1);
    if(res==EQUAL){
      res = Int::compare(f1,f2);
    }
    return res;
  }
};

struct FnRevFreqComparator
{
  Comparison compare(unsigned f1, unsigned f2)
  {
    unsigned c1 = env.signature->getFunction(f1)->usageCnt();
    unsigned c2 = env.signature->getFunction(f2)->usageCnt();
    Comparison res = Int::compare(c1,c2);
    if(res==EQUAL){
      res = Int::compare(f1,f2);
    }
    return res;
  }
};
struct PredRevFreqComparator
{
  Comparison compare(unsigned p1, unsigned p2)
  {
    unsigned c1 = env.signature->getPredicate(p1)->usageCnt();
    unsigned c2 = env.signature->getPredicate(p2)->usageCnt();
    Comparison res = Int::compare(c1,c2);
    if(res==EQUAL){
      res = Int::compare(p1,p2);
    }
    return res;
  }
};

struct FnArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u1),
	    env.signature->functionArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u1),
	    env.signature->predicateArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};

struct FnRevArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u2),
	    env.signature->functionArity(u1));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredRevArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u2),
	    env.signature->predicateArity(u1));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};

static void loadPermutationFromString(DArray<unsigned>& p, const vstring& str) {
  CALL("loadPermutationFromString");

  std::stringstream ss(str.c_str());
  unsigned i = 0;
  unsigned val;
  while (ss >> val)
  {
      if (i >= p.size()) {
        break;
      }

      if (val >= p.size()) {
        break;
      }

      p[i++] = val;

      if (ss.peek() == ',')
          ss.ignore();
  }
}
*/

struct FnFreqComparator
{
  Comparison compare(unsigned f1, unsigned f2)
  {
    unsigned c1 = env.signature->getFunction(f1)->usageCnt();
    unsigned c2 = env.signature->getFunction(f2)->usageCnt();
    Comparison res = Int::compare(c2,c1);
    if(res==EQUAL){
      res = Int::compare(f1,f2);
    }
    return res;
  }
};

struct PredFreqComparator
{
  Comparison compare(unsigned p1, unsigned p2)
  {
    unsigned c1 = env.signature->getPredicate(p1)->usageCnt();
    unsigned c2 = env.signature->getPredicate(p2)->usageCnt();
    Comparison res = Int::compare(c2,c1);
    if(res==EQUAL){
      res = Int::compare(p1,p2);
    }
    return res;
  }
};

template<typename T> struct ArrayValueComparator
{
  const DArray<T>& _values;
  ArrayValueComparator(const DArray<T>& values) : _values(values) {}

  Comparison compare(unsigned i1, unsigned i2)
  {
    Comparison res = Int::compare(_values[i1],_values[i2]);
    if(res==EQUAL){
      res = Int::compare(i1,i2);
    }
    return res;
  }
};

struct FunctionLookupProxy {
  const char* myname() { return "function"; }
  const char* myName() { return "Function"; }

  bool exists(const vstring& name, unsigned arity) { return env.signature->functionExists(name,arity); }
  unsigned getNumber(const vstring& name, unsigned arity) { return env.signature->getFunctionNumber(name,arity); }
  const vstring getName(unsigned i) { return env.signature->functionName(i); }
  unsigned getArity(unsigned i) { return env.signature->functionArity(i); }

  FnFreqComparator getComparator() { return FnFreqComparator(); }

  bool userPreferenceEmpty(const Options& opt) { return opt.functionPrecedence().empty(); }
  const vstring& getUserPreferenceString(const Options& opt) { return opt.functionPrecedence(); }
  bool userPreferenceFileNameEmpty(const Options& opt) { return opt.functionPrecedenceFile().empty(); }
  const char* getUserPreferenceFileName(const Options& opt) { return opt.functionPrecedenceFile().c_str(); }
};

struct PredicateLookupProxy {
  const char* myname() { return "predicate"; }
  const char* myName() { return "Predicate"; }

  bool exists(const vstring& name, unsigned arity) { return env.signature->predicateExists(name,arity); }
  unsigned getNumber(const vstring& name, unsigned arity) { return env.signature->getPredicateNumber(name,arity); }
  const vstring getName(unsigned i) { return env.signature->predicateName(i); }
  unsigned getArity(unsigned i) { return env.signature->predicateArity(i); }

  PredFreqComparator getComparator() { return PredFreqComparator(); }

  bool userPreferenceEmpty(const Options& opt) { return opt.predicatePrecedence().empty(); }
  const vstring& getUserPreferenceString(const Options& opt) { return opt.predicatePrecedence(); }
  bool userPreferenceFileNameEmpty(const Options& opt) { return opt.predicatePrecedenceFile().empty(); }
  const char* getUserPreferenceFileName(const Options& opt) { return opt.predicatePrecedenceFile().c_str(); }
};

template<typename T> // T encapsulates access to either functions or predicates in the signature
static void parseUserPreferenceLine(DArray<unsigned>& p, const std::string& line, T thing) {
  CALL("parseUserPreferenceLine");
  std::stringstream ss(line);

  vstring name;
  unsigned arity;
  unsigned value;
  if (!(ss >> name >> arity >> value)) {
    cerr << "WARNING: Weird line in " << thing.myname() << " preference spec: " << line << endl; // "function"
    return;
  }

  if (!name.empty() && name[name.length()-1] == '*') {
    // terminal wild card matching (= search string should be a prefix) -- slow
    for (unsigned i = 0; i < p.size(); i++) {
      if (thing.getName(i).compare(0,name.length()-1,name,0,name.length()-1) == 0) { // match // env.signature->functionName(i)
        p[i] = value;
      }
    }
  } else {
    // efficient lookup for a precise match
    if (!thing.exists(name,arity)) { // env.signature->functionExists(name,arity)
      cerr << "WARNING: " << thing.myName() << " " << name << "/" << arity << " does not exist." << endl; // "Function"
      return;
    }

    unsigned i = thing.getNumber(name,arity); // env.signature->getFunctionNumber(name,arity);

    p[i] = value;
  }
}

template<typename T> // T encapsulates access to either functions or predicates in the signature
static void loadUserPreferencesFromFile(DArray<unsigned>& p, const char* filename, T thing) {
  CALL("loadUserValuesFromFile");

  BYPASSING_ALLOCATOR;

  ifstream preference_file (filename);
  if (preference_file.is_open()) {
    std::string line;
    while (getline(preference_file, line)) {
      parseUserPreferenceLine(p,line,thing);
    }

    preference_file.close();
  }
}

template<typename T> // T encapsulates access to either functions or predicates in the signature
static void loadUserPreferencesFromString(DArray<unsigned>& p, const vstring& string, T thing) {
  CALL("loadUserPreferencesFromString");

  BYPASSING_ALLOCATOR;

  std::stringstream ss(string.c_str());
  std::string line;
  while (std::getline(ss, line, '#')) {
    parseUserPreferenceLine(p,line,thing);
  }

}

template <typename T>
static void initPrecedenece(const Options& opt, unsigned numOfThings, DArray<int>& precedence, T thing) {
  static DArray<unsigned> aux(32);
  static DArray<int> values(32);
  int coef;

  if(numOfThings) {
    values.init(numOfThings,0);

    coef = opt.symbolPrecedenceOccurrenceCoef();
    if (coef) {
      // the array is naturally created ordered by occurrence
      for (unsigned i = 0; i < numOfThings; i++) {
        values[i] += coef*i;
      }
    }

    coef = opt.symbolPrecedenceArityCoef();
    if (coef) {
      for (unsigned i = 0; i < numOfThings; i++) {
        values[i] += coef*thing.getArity(i);
      }
    }

    coef = opt.symbolPrecedenceFrequencyCoef();
    if (coef) {
      aux.initFromIterator(getRangeIterator(0u, numOfThings), numOfThings);
      aux.sort(thing.getComparator());

      for (unsigned i = 0; i < numOfThings; i++) {
        // cout << "aux " << i << " for " << thing.getName(i) << " val " <<  aux[i] << endl;

        values[aux[i]] += coef*i;
      }
    }

    coef = opt.symbolPrecedenceUserCoef();
    if (coef && !(thing.userPreferenceFileNameEmpty(opt) && thing.userPreferenceEmpty(opt))) {
      aux.init(numOfThings,0);
      if (!thing.userPreferenceFileNameEmpty(opt)) {
        loadUserPreferencesFromFile(aux,thing.getUserPreferenceFileName(opt),thing);
      }
      if (!thing.userPreferenceEmpty(opt)) {
        loadUserPreferencesFromString(aux,thing.getUserPreferenceString(opt),thing);
      }

      for (unsigned i = 0; i < numOfThings; i++) {
        values[i] += coef*aux[i];
      }
    }

    // here we sort aux by values
    aux.initFromIterator(getRangeIterator(0u, numOfThings), numOfThings);
    aux.sort(ArrayValueComparator<int>(values));

    cout << thing.myName() << " precedences:" << endl;
    for(unsigned i=0;i<numOfThings;i++){
      cout << thing.getName(aux[i]) << " ";
    }
    cout << endl;

    cout << thing.myName() << " precedence: ";
    for(unsigned i=0;i<numOfThings;i++){
      cout << aux[i] << ",";
    }
    cout << endl;

    for(unsigned i=0;i<numOfThings;i++) {
      precedence[aux[i]]=i;
    }
  }
}

/**
 * Create a KBOBase object.
 */
KBOBase::KBOBase(Problem& prb, const Options& opt)
  : _predicates(env.signature->predicates()),
    _functions(env.signature->functions()),
    _predicateLevels(_predicates),
    _predicatePrecedences(_predicates),
    _functionPrecedences(_functions)
{
  CALL("KBOBase::KBOBase");
  ASS_G(_predicates, 0);

  /*
  for (unsigned i = 0; i < _functions; i++) {
    cout << env.signature->functionName(i) << " has usage count " << env.signature->getFunction(i)->usageCnt() << endl;
  }
  */

  initPrecedenece(opt,_functions,_functionPrecedences,FunctionLookupProxy());
  initPrecedenece(opt,_predicates,_predicatePrecedences,PredicateLookupProxy());

  switch(opt.literalComparisonMode()) {
  case Shell::Options::LiteralComparisonMode::STANDARD:
    _predicateLevels.init(_predicates, 1);
    break;
  case Shell::Options::LiteralComparisonMode::PREDICATE:
  case Shell::Options::LiteralComparisonMode::REVERSE:
    for(unsigned i=1;i<_predicates;i++) {
      _predicateLevels[i]=_predicatePrecedences[i]+1;
    }
    break;
  }
  //equality is on the lowest level
  _predicateLevels[0]=0;

  _reverseLCM = opt.literalComparisonMode()==Shell::Options::LiteralComparisonMode::REVERSE;

  for(unsigned i=1;i<_predicates;i++) {
    Signature::Symbol* predSym = env.signature->getPredicate(i);
    //consequence-finding name predicates have the lowest level
    if(predSym->label()) {
      _predicateLevels[i]=-1;
    }
    else if(predSym->equalityProxy()) {
      //equality proxy predicates have the highest level (lower than colored predicates)
      _predicateLevels[i]=_predicates+2;
    }

  }
}


}

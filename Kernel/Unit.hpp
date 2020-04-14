
/*
 * File Unit.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Unit.hpp
 * Defines class Unit for all kinds of proof units
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __Unit__
#define __Unit__

#include "Forwards.hpp"

#include "Lib/List.hpp"
#include "Lib/VString.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;

/**
 * Class to represent units of inference (such as clauses and formulas).
 * @since 08/05/2007 Manchester
 */
class Unit
{
protected:
  ~Unit() {}
public:
  /** Kind of unit. The integers should not be changed, they are used in
   *  Compare.
   */
  enum Kind {
    /** Clause unit */
    CLAUSE = 0,
    /** Formula unit */
    FORMULA = 1
  };

  void destroy();
  vstring toString() const;
  unsigned varCnt();

  vstring inferenceAsString() const;

  /** True if a clause unit */
  bool isClause() const
  { return _kind == CLAUSE; }

  Clause* asClause();

  /** Return the number of this unit */
  unsigned number() const { return _number; }

  /** Return the inference of this unit */
  Inference* inference() { return _inference; }
  /** Return the inference of this unit */
  const Inference* inference() const { return _inference; }
  /** Set a new inference object (the old one not destroyed). */
  void setInference(Inference* inf) { _inference = inf; }

  /** Return the inherited color of the unit or COLOR_INVALID
   * if there isn't an inherited color.
   *
   * Inherited color is set by parser constructs left_formula,
   * right_formula and end_formula.
   */
  inline Color inheritedColor() const
  {
    return static_cast<Color>(_inheritedColor);
  }
  void setInheritedColor(Color color)
  {
    ASS_NEQ(color,COLOR_INVALID);
    _inheritedColor = color;
  } // setInheritedColor

  void invalidateInheritedColor() { _inheritedColor = COLOR_INVALID; }

  Color getColor();
  unsigned getWeight();

  Formula* getFormula();
  void collectAtoms(Stack<Literal*>& acc);
  void collectPredicates(Stack<unsigned>& acc);

  /**
   * Increase the number of references to the unit.
   *
   * Only clauses are reference-counted, for FormulaUnits nothing
   * is done.
   */
  void incRefCnt();
  /**
   * Decrease the number of references to the unit.
   *
   * Only clauses are reference-counted, for FormulaUnits nothing
   * is done.
   */
  void decRefCnt();

  /** mark the unit as read from a TPTP included file  */
  inline void markIncluded() {_included = 1;}
  /** true if the unit is read from a TPTP included file  */
  inline bool included() const {return _included;}

  /** Return true iff unit was created during preprocessing
   * (and not during the run of the saturation algorithm) */
  inline bool isFromPreprocessing()
  { return !_firstNonPreprocessingNumber || _number<_firstNonPreprocessingNumber; }

  void assertValid();

  static void onPreprocessingEnd();
  static void onParsingEnd(){ _lastParsingNumber = _lastNumber;}
  static unsigned getLastParsingNumber(){ return _lastParsingNumber;}

protected:
  /** Number of this unit, used for printing and statistics */
  unsigned _number;
  /** Kind  */
  unsigned _kind : 1;
  /** used in interpolation to denote parents of what color have been used */
  unsigned _inheritedColor : 2;
  /** true if the unit is read from a TPTP included file  */
  unsigned _included : 1;
  /** inference used to obtain the unit */
  Inference* _inference;

  Unit(Kind kind,Inference* inf);

  /** Used to enumerate units */
  static unsigned _lastNumber;

  /** Used to determine which clauses come from preprocessing
   *
   * 0 means preprocessing is not over yet.*/
  static unsigned _firstNonPreprocessingNumber;

  static unsigned _lastParsingNumber;
}; // class Unit

std::ostream& operator<< (ostream& out, const Unit& u );

}
#endif

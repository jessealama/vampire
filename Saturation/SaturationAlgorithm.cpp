/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;


SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainerSP passiveContainer,
	LiteralSelectorSP selector)
: _imgr(this), _passive(passiveContainer), _generator(0), _fwSimplifier(0),
_bwSimplifier(0), _selector(selector)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();

#if VDEBUG
//  enableContainerPrintouts();
#endif
}

SaturationAlgorithm::~SaturationAlgorithm()
{
  if(_generator) {
    _generator->detach();
  }
  if(_fwSimplifier) {
    _fwSimplifier->detach();
  }
  if(_bwSimplifier) {
    _bwSimplifier->detach();
  }

  delete _unprocessed;
  delete _active;
}

void SaturationAlgorithm::setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator)
{
  ASS(!_generator);
  _generator=generator;
  _generator->attach(this);
}
void SaturationAlgorithm::setForwardSimplificationEngine(ForwardSimplificationEngineSP fwSimplifier)
{
  ASS(!_fwSimplifier);
  _fwSimplifier=fwSimplifier;
  _fwSimplifier->attach(this);
}
void SaturationAlgorithm::setBackwardSimplificationEngine(BackwardSimplificationEngineSP bwSimplifier)
{
  ASS(!_bwSimplifier);
  _bwSimplifier=bwSimplifier;
  _bwSimplifier->attach(this);
}

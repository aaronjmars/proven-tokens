# Run by mk_config.py (exec, with the dict `cfg` in scope): the axioms test. The hand-written
# theorems of the streams (reclaim, reentrancy, readable, witnesses) are listed in
# config/axioms_names.json; gen_axioms.py adds the generated ones and the witnesses of
# work/sanity_names.json. No skip list; declared_only leaves out generated names that no Lean
# file declares (the fallbacks and the segments of reclaimToken have no supply theorem).
import json as _json
cfg['generators'] = cfg['generators'] + ['axioms']
cfg['axioms'] = {
    'declared_only': True, 'dotted_decl': True,
    'imports': ['WbtcVerify.Wbtc.Invariant'],
    'names': ['CODE_eq', 'size_CODE', 'and_div_selector', 'div_and_selector', 'mask_idem',
              'mask_lt'],
    'after': _json.load(open(os.path.join(HERE, '..', 'config', 'axioms_names.json')))['after'],
}

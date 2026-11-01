# C3: t=2 AbsWNxU consumer chain

Scope: make a parallel U path for the V3 t=2 entry, without changing existing Lean files. `AbsWNxU` admits the measured `UpgAbsShape`; the old `AbsWNx` does not. The active route is through `T2BelowAtV3` and `V3T2RootV3`.

|File / declaration|Use of old boundary|U-port needed?|
|---|---|---|
|`WfT2X2.lean:30` `not_bd_of_cl`|Reads `CL M i = []` from `hBdS`; no value or absorption field.|Yes; use `hBdCL` directly.|
|`WfT2X2.lean:36` `good_below_ofX`|Consumes `hBdS` at a bad final counted child to obtain its parent/child shape; calls `bad_frame`. Also calls `not_bd_of_cl`.|Yes; `good_below_ofXU` uses `hBdF` and calls `bad_frameG` when the allowance is not the immediate parent.|
|`WfT2X2.lean:215` `t2_assembleOTX`|Builds the lower `PX` callback via `deps_lhd_otX`, passing `hBdS`; then calls `good_below_ofX`.|Yes; `t2_assembleOTXU` passes `hBdUp`, `hBdF`, `hBdK`, and `hBdCL`.|
|`WfT2X3.lean:53` `t2_sv_belowX`|Turns `AbsWNx` into `AbsAt ∨ BdX` with `bdx_absX`, supplies `bdx_shape`, then calls `t2_assembleOTX`.|Yes; U version uses `bdxu_absX`, `bdxu_up/F/cl`, `NotBumpKidXU`.|
|`WfT2X3.lean:219` `t2_qr_belowX`|Same old bad-set construction and assembly call.|Yes; `t2_qr_belowXU`.|
|`WfT2X3.lean:447` `t2_qn_belowX`|Same old bad-set construction and assembly call.|Yes; `t2_qn_belowXU`.|
|`WfT2X4.lean:20` `T2BelowResX`|Record contains `AbsWNx ∧ NotBumpKidX`.|Yes; define `T2BelowResXU` with `AbsWNxU ∧ NotBumpKidXU`.|
|`WfT2X4.lean:31` `T2BelowRes.toX` and `:45` `T2BelowXResAt.toX`|Convert the old residual to the old X residual.|Keep old theorem; add `toXU` from `AbsWNx.toU` and `notBumpKidXU_of`.|
|`WfT2X4.lean:61` `t2BelowXS_ofX`|Uses the three X below engines; this is the constructor for `T2BelowXSX`.|Yes; copy as `t2BelowXS_ofXU` and call U engines.|
|`WfT2X4.lean:310` `t2BelowXAll_ofX`, `:316` `t2BelowXE_ofX`|Propagate the old X residual into all/existential expansion outputs.|Yes; U versions needed by V3 below/carrier.|
|`WfT2R4.lean:18` `t2_assembleRootX`|Root analogue of the lower assembler; passes `hBdS` to `deps_lhd_otX`, `bdx_absX`, `bdx_shape`, and `NotBumpKidX`.|Yes; `t2_assembleRootXU`.|
|`WfT2R4.lean:202,369,573` root engines `t2_sv_rootX`, `t2_qr_rootX`, `t2_qn_rootX`|Each uses `AbsWNx`, old bad-set facts, and root assembler.|Yes; U versions call U assembler and U shape facts.|
|`WfT2R5.lean:15` `t2_root_ofX`|Combines the three root engines into root descent for every expansion.|Yes; `t2_root_ofXU`.|
|`V3T2BelowV3.lean:15` `T2BelowAtV3`|Source-frame record wraps `T2BelowResX`.|Yes; parallel `T2BelowAtV3U` wraps `T2BelowResXU`.|
|`V3T2BelowV3.lean:20,270` `t2BelowXS_V3`, `t2BelowXE_V3`|Constructs expansion frame/Good3 facts from the old source residual using old below engines.|Yes; `t2BelowXS_V3U` / `t2BelowXE_V3U` use U residual and engines.|
|`V3T2RootV3.lean:13` `t2_rootV3`|Uses `T2BelowAtV3` and `t2_root_ofX`.|Yes; `t2_rootV3U` uses U variants.|
|`V3T2CarrierV3.lean:13` `t2_carrierV3`|Consumes `T2BelowAtV3` in both `t2BelowXE_V3` and `t2_rootV3`.|Yes; `t2_carrierV3U`.|
|`V3TranslationInputsV3.lean:29` `expOut2_of_inputs`|The `hBX` input is `T2AtV3 T2BelowAtV3`; passes it to the carrier.|Yes; new entry uses `T2AtV3 T2BelowAtV3U`.|
|`V3TranslationStepV3.lean:22-39` step entry points|Propagate old `hBX` into `expOut2_of_inputs`.|Yes; new `V3TranslationAbsUV3.lean` entry points with `hBXU`.|

## Adjacent but not on the active V3 path

- `WfT2R7.lean` onward packages the older V2/XR residual (`T2BelowXResV2X`, `R2V2X`, old top wrappers). It refers to the same old `AbsWNx`/`NotBumpKidX` definitions, but `V3T2BelowV3 → V3T2RootV3 → V3T2CarrierV3 → V3Translation...` does not import or call those wrappers. Do not port them for this C3 entry.
- `WfT2R8.lean` top theorem still uses the XR/V2 chain; `WfT2R9.lean` removes only the structural `NotBumpKidX` field. Neither is a dependency of the requested U entry.

## Port order

`WfT2X2U` → `WfT2X3U` → `WfT2X4U` → `WfT2R4U` → `WfT2R5U` → `V3T2BelowV3U` → `V3T2RootV3U` → `V3T2CarrierV3U` → `V3TranslationAbsUV3`.

## Foreign-allowance frame readers

The first U chain returned `FrameShapeXU`, but the original readers in X5-X7 and the
path-level helpers in R1 accepted only `FrameShapeX`. The parallel reader modules now
cover the widened shape:

- `WfT2X5U`: `frame_of_shapeXU`, `rw_frame_of_shapeXU`, and
  `clField_of_shapeSXU`. The `FrameShapeX` branch delegates to the old reader; the
  `FrameShape5` branch uses `shape4_split` and its component bound.
- `WfT2X6U`: `qVSF_of_shapeXU`; its fifth-shape branch uses
  `vs_changed_boundVG` with the frame's foreign allowance.
- `WfT2X7U`: low-value lemmas `qFC_lowVG`, `qFCo_lowVG`, `qVRAt_lowVG`, and
  `qFO_lowVG`. The fields are unchanged by the argument-free lowered child.
- `WfT2R1U`: path-level readers `pathLv_of_shapeXRU` and
  `pathLvAll_pre_t2XRU`, using `FrameShapeXU` and `frame_of_shapeXU`.

These modules are parallel helpers; existing X5-X7/R1 files were not modified.

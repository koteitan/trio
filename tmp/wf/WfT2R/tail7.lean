
namespace Ytosk

/-- **`R2V2X` from `T2BelowXResV2X`** (`r2V2_of` without `absN`). -/
theorem r2V2_ofXR (hB : WfT2X.T2BelowXResV2X) : R2V2X := fun M ρ rk C hz h2 =>
  r2X_t2XR (hB M ρ rk C) t2Seed1SV_holds t2Seed1C_holds C.std (Inv3W.ofV2 C.S C.I) C.toW hz h2

end Ytosk

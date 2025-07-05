import Std.Tactic.BVDecide

theorem bvand_distr_over_bvor:
    ∀ (a b c: BitVec 64), a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
      bv_decide

theorem bv_distr_over_u64and:
    ∀ (a b : UInt64), (a &&& b).toBitVec = (a.toBitVec &&& b.toBitVec) := by
      simp

theorem u64_bv_roundtrip: ∀ (a: UInt64), a.toBitVec.toNat.toUInt64 = a := by
  simp

theorem bv_u64_roundtrip: ∀ (bv: BitVec 64), bv.toNat.toUInt64.toBitVec = bv := by
  simp

theorem u64and_eq_bvand:
    ∀ (a b : UInt64), a &&& b = (a.toBitVec &&& b.toBitVec).toNat.toUInt64 := by
      simp

theorem bv_distr_over_u64or:
    ∀ (a b : UInt64), (a ||| b).toBitVec = (a.toBitVec ||| b.toBitVec) := by
      bv_decide

theorem u64or_eq_bvor:
    ∀ (a b : UInt64), a ||| b = (a.toBitVec ||| b.toBitVec).toNat.toUInt64 := by
      simp

-- alternatively, this theorem can be directly proved by the bv solver:
-- bv_decide
theorem u64and_dist_over_or:
    ∀ (a b c : UInt64), a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
      intros a b c
      repeat rewrite [u64and_eq_bvand]
      repeat rewrite [u64or_eq_bvor]
      repeat rewrite [bv_u64_roundtrip]
      rewrite [bvand_distr_over_bvor]
      rfl


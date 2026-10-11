import MobiusLean.Numeric
import MobiusLean.Lucas
import MobiusLean.Brute
import MobiusLean.Word
import MobiusLean.Controls
import MobiusLean.ControlsLight
import MobiusLean.Prepass
import MobiusLean.LucasE1
import MobiusLean.ControlsPrepass

/-! Every theorem depends only on Lean's standard axioms (no `sorryAx`, no `native_decide`, no `Lean.ofReduceBool`). -/

#print axioms Mob.v_eq_choose
#print axioms Mob.c_eq_choose
#print axioms Mob.d_eq_choose
#print axioms Mob.delta_closed
#print axioms Mob.consts_92
#print axioms Mob.Wstar_92
#print axioms Mob.delta_92
#print axioms Mob.delta_pos_79_92
#print axioms Mob.delta_neg_78
#print axioms Mob.eps_bounds
#print axioms Mob.log_m_mem
#print axioms Mob.eps_pos
#print axioms Mob.eps_lt_one
#print axioms Mob.m_pos
#print axioms Mob.log_m_pos
#print axioms Mob.theta_lt_one
#print axioms Mob.theta_pos
#print axioms Mob.one_sub_theta
#print axioms Mob.one_sub_theta_bounds
#print axioms Mob.filter_card_le_two
#print axioms Mob.centre_count
#print axioms Mob.lucas_table
#print axioms Mob.lucas_gadget
#print axioms Mob.lucas_identity_h6
#print axioms Mob.lucas_identity_h7
#print axioms Mob.counts_h8
#print axioms Mob.counts_h9
#print axioms Mob.counts_h10
#print axioms Mob.W.field_ok_true
#print axioms Mob.W.inv_ok_true
#print axioms Mob.W.omega_ok
#print axioms Mob.W.kernel_ok
#print axioms Mob.W.s1_ok
#print axioms Mob.W.factors_ok
#print axioms Mob.W.word_ok
#print axioms Mob.ctl_Wstar_54
#print axioms Mob.ctl_delta_78
#print axioms Mob.ctl_eps_lo
#print axioms Mob.ctl_eps_hi
#print axioms Mob.ctl_theta_lo
#print axioms Mob.ctl_log_m
#print axioms Mob.ctl_centre_small
#print axioms Mob.ctl_no_J
#print axioms Mob.ctl_mod2
#print axioms Mob.ctl_d_formula
#print axioms Mob.ctl_word
#print axioms Mob.ctl_s1
#print axioms Mob.ctl_kernel
#print axioms Mob.vE_eq_choose
#print axioms Mob.cE_eq_choose
#print axioms Mob.dE_eq_choose
#print axioms Mob.delta2_closed
#print axioms Mob.deltaE_closed
#print axioms Mob.delta2_pos_43_120
#print axioms Mob.delta2_neg_4_42
#print axioms Mob.deltaE_pos_20_60
#print axioms Mob.deltaE_neg_7_19
#print axioms Mob.consts_51
#print axioms Mob.Wstar_51
#print axioms Mob.constsE_23
#print axioms Mob.WstarE_23
#print axioms Mob.spot_values
#print axioms Mob.one_sub_thetaOf
#print axioms Mob.thetaOf_lt_one
#print axioms Mob.thetaOf_pos
#print axioms Mob.one_sub_thetaOf_mem
#print axioms Mob.eps51_bounds
#print axioms Mob.log_m51_mem
#print axioms Mob.theta1p_lt_one
#print axioms Mob.one_sub_theta1p_bounds
#print axioms Mob.theta1p_pos
#print axioms Mob.epsE23_bounds
#print axioms Mob.log_m23_mem
#print axioms Mob.theta2_lt_one
#print axioms Mob.one_sub_theta2_bounds
#print axioms Mob.theta2_pos
#print axioms Mob.centre3_count
#print axioms Mob.centre3_table
#print axioms Mob.e1_gadget
#print axioms Mob.ctl_delta2_42
#print axioms Mob.ctl_deltaE_19
#print axioms Mob.ctl_deltaE1_20
#print axioms Mob.ctl_Wstar_51
#print axioms Mob.ctl_WstarE_23
#print axioms Mob.ctl_eps51
#print axioms Mob.ctl_epsE23
#print axioms Mob.ctl_theta1p_lo
#print axioms Mob.ctl_theta2_lo
#print axioms Mob.ctl_theta2_hi
#print axioms Mob.ctl_centre2
#print axioms Mob.ctl_centre_le2_on7
#print axioms Mob.ctl_noJ_E1

import IpadAgent.Model
import IpadAgent.Transition
import IpadAgent.Reachability
import IpadAgent.Invariants
import IpadAgent.Scenario

/-!
入口模块：按学习顺序导入模型、迁移关系、可达性、不变式和场景。
运行 `lake build` 可检查所有模块及其证明。
-/

open IpadAgent

/-! ### 公理审计：检查定理依赖的公理 -/
#print axioms provisioned_implies_paired
#print axioms exec_implies_provisioned
#print axioms roAllow_fixed
#print axioms approved_wf
#print axioms executed_wf
#print axioms exec_approved_or_allowlisted
#print axioms nonce_nodup
#print axioms bytes_binding
#print axioms readLogs_frame
#print axioms side_effect_requires_approval
#print axioms audit_append_only
#print axioms scenario_reachable

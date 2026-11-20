import IpadAgent.Model

/-!
### 2. 迁移语义

`Act` 表示外部请求；`Step` 的每个构造子定义一种允许的状态变化。把规则写成 `Prop` 关系后，证明可以按迁移规则分类讨论。
-/
namespace IpadAgent

inductive Act where
  | sshAuth     (ok : Bool)
  | initSandbox (ok : Bool)
  | readLogs
  | propose     (sc : Script)
  | approve     (bytes : String) (nonce : Nat)
  | exec        (sc : Script) (nonce : Nat)
  deriving Repr

/--
单步迁移。执行拆成两条规则：白名单内免审批且不改状态；白名单外必须审批并视为有副作用。
拆成构造子后，证明可以直接区分两种情况，而不需要在抽象哈希上计算条件表达式。
-/
inductive Step (hash : String → Digest) : St → Act → St → Prop where
  | sshAuth_ok {s : St} (h : s.paired = false) :
      Step hash s (.sshAuth true) { s with paired := true, audit := "ssh.auth.ok" :: s.audit }
  | sshAuth_fail {s : St} :
      Step hash s (.sshAuth false) { s with audit := "ssh.auth.fail" :: s.audit }
  | init_ok {s : St} (hp : s.paired = true) (hi : s.provisioned = false) :
      Step hash s (.initSandbox true) { s with provisioned := true, audit := "init.sandbox.ok" :: s.audit }
  | init_fail {s : St} (hp : s.paired = true) :
      Step hash s (.initSandbox false) { s with audit := "init.sandbox.fail" :: s.audit }
  | readLogs {s : St} :
      Step hash s .readLogs { s with audit := "logs.read" :: s.audit }
  | propose {s : St} (sc : Script) :
      Step hash s (.propose sc) { s with audit := "propose" :: s.audit }
  | approve {s : St} (b : String) (n : Nat) :
      Step hash s (.approve b n)
        { s with approved := ({ digest := hash b, nonce := n, bytes := b } : Appr) :: s.approved,
                 audit := "approve" :: s.audit }
  | exec_ro {s : St} (sc : Script) (n : Nat)
      (hprov : s.provisioned = true)
      (hro : hash sc.bytes ∈ s.roAllow)
      (hfresh : ∀ r ∈ s.executed, r.nonce ≠ n) :
      Step hash s (.exec sc n)
        { s with executed := ({ digest := hash sc.bytes, nonce := n, bytes := sc.bytes } : Exec) :: s.executed,
                 audit := "exec.ro" :: s.audit }
  | exec_side {s : St} (sc : Script) (n : Nat)
      (hprov : s.provisioned = true)
      (hnotro : hash sc.bytes ∉ s.roAllow)
      (happr : ({ digest := hash sc.bytes, nonce := n, bytes := sc.bytes } : Appr) ∈ s.approved)
      (hfresh : ∀ r ∈ s.executed, r.nonce ≠ n) :
      Step hash s (.exec sc n)
        { s with executed := ({ digest := hash sc.bytes, nonce := n, bytes := sc.bytes } : Exec) :: s.executed,
                 xrayRunning := true,
                 audit := "exec.side" :: s.audit }

end IpadAgent

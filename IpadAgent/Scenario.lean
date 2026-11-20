import IpadAgent.Invariants

/-!
### 5. 场景构造

给出一条具体执行轨迹，证明模型不只是禁止所有操作：只读日志可以免审批，
而配置修改与重启需要匹配的审批记录。
-/
namespace IpadAgent

variable {hash : String → Digest}

/-- 内置只读工具：读取 xray 日志（`roToolBodies` 的第一条）。 -/
def scRead : Script :=
  { bytes := "cat /var/log/xray/error.log | tail -n 200", prov := Prov.agent }

/-- Agent 分析日志后生成的修复脚本：备份、修改配置、预检、重启。 -/
def scFix : Script :=
  { bytes := "cp /usr/local/etc/xray/config.json /tmp/cfg.bak && sed -i 's#127.0.0.1:1080#0.0.0.0:1080#' /usr/local/etc/xray/config.json && xray run -test -c /usr/local/etc/xray/config.json && systemctl restart xray",
    prov := Prov.logTainted }

/-- 假设修复脚本不等同于任何内置只读工具（哈希层面）。 -/
def NotReadOnly (hash : String → Digest) (sc : Script) : Prop :=
  hash sc.bytes ∉ roToolBodies.map hash

/--
INV-10：完整场景可达。读日志免审批，修改与重启需要一次签名，
最终留下两条执行记录与一条审批。
-/
theorem scenario_reachable (hfix : NotReadOnly hash scFix) :
    ∃ s : St, Reachable hash s ∧ s.paired = true ∧ s.provisioned = true ∧
      s.xrayRunning = true ∧ s.executed.length = 2 ∧
      (∃ a ∈ s.approved, a.bytes = scFix.bytes) := by
  let s0 : St := initSt hash
  have hro : hash scRead.bytes ∈ s0.roAllow := by
    simp [s0, initSt, roToolBodies, scRead]
  let s1 : St := { s0 with paired := true, audit := "ssh.auth.ok" :: s0.audit }
  let s2 : St := { s1 with provisioned := true, audit := "init.sandbox.ok" :: s1.audit }
  let s3 : St := { s2 with audit := "logs.read" :: s2.audit }
  let s4 : St := { s3 with audit := "propose" :: s3.audit }
  let e1 : Exec := { digest := hash scRead.bytes, nonce := 11, bytes := scRead.bytes }
  let s5 : St := { s4 with executed := (e1 :: s4.executed), audit := "exec.ro" :: s4.audit }
  let s6 : St := { s5 with audit := "propose" :: s5.audit }
  let a2 : Appr := { digest := hash scFix.bytes, nonce := 22, bytes := scFix.bytes }
  let s7 : St := { s6 with approved := (a2 :: s6.approved), audit := "approve" :: s6.audit }
  let e2 : Exec := { digest := hash scFix.bytes, nonce := 22, bytes := scFix.bytes }
  let s8 : St := { s7 with executed := (e2 :: s7.executed), xrayRunning := true, audit := "exec.side" :: s7.audit }
  -- ① 输入 VPS 的 SSH 信息并认证
  have st1 : Step hash s0 (.sshAuth true) s1 := by
    have h : s0.paired = false := by simp [s0, initSt]
    simpa [s1] using Step.sshAuth_ok (hash := hash) (s := s0) h
  -- ② SSH 下发沙箱初始化命令
  have st2 : Step hash s1 (.initSandbox true) s2 := by
    have hp : s1.paired = true := by simp [s1]
    have hi : s1.provisioned = false := by simp [s0, s1, initSt]
    simpa [s2] using Step.init_ok (hash := hash) (s := s1) hp hi
  -- ③ 读取 xray 日志
  have st3 : Step hash s2 .readLogs s3 := by
    simpa [s3] using Step.readLogs (hash := hash) (s := s2)
  -- ④ 提交并执行只读工具（命中白名单，免审批）
  have st4 : Step hash s3 (.propose scRead) s4 := by
    simpa [s4] using Step.propose (hash := hash) (s := s3) scRead
  have st5 : Step hash s4 (.exec scRead 11) s5 := by
    have h1 : s4.provisioned = true := by simp [s2, s3, s4]
    have h2 : hash scRead.bytes ∈ s4.roAllow := by simpa [s0, s1, s2, s3, s4] using hro
    have h3 : ∀ r ∈ s4.executed, r.nonce ≠ 11 := by
      intro r hr; simp [s0, s1, s2, s3, s4, initSt] at hr
    simpa [s5, e1] using Step.exec_ro (hash := hash) (s := s4) scRead 11 h1 h2 h3
  -- ⑤ Agent 根据日志提出修复脚本
  have st6 : Step hash s5 (.propose scFix) s6 := by
    simpa [s6] using Step.propose (hash := hash) (s := s5) scFix
  -- ⑥ 用户确认：Secure Enclave 对脚本全文哈希签名
  have st7 : Step hash s6 (.approve scFix.bytes 22) s7 := by
    simpa [s7, a2] using Step.approve (hash := hash) (s := s6) scFix.bytes 22
  -- ⑦ 执行修改并重启（白名单外，因此必须已有审批）
  have st8 : Step hash s7 (.exec scFix 22) s8 := by
    have h1 : s7.provisioned = true := by simp [s2, s3, s4, s5, s6, s7]
    have h2 : hash scFix.bytes ∉ s7.roAllow := by
      intro hmem
      exact hfix (by simpa [s0, s1, s2, s3, s4, s5, s6, s7, initSt] using hmem)
    have h3 : ({ digest := hash scFix.bytes, nonce := 22, bytes := scFix.bytes } : Appr) ∈ s7.approved := by
      simp [s7, a2]
    have h4 : ∀ r ∈ s7.executed, r.nonce ≠ 22 := by
      intro r hr
      simp [s0, s1, s2, s3, s4, s5, s6, s7, e1, initSt] at hr
      subst hr
      simp
    simpa [s8, e2] using Step.exec_side (hash := hash) (s := s7) scFix 22 h1 h2 h3 h4
  have h8 : Reachable hash s8 :=
    Reachable.step
      (Reachable.step
        (Reachable.step
          (Reachable.step
            (Reachable.step
              (Reachable.step
                (Reachable.step
                  (Reachable.step Reachable.init st1) st2) st3) st4) st5) st6) st7) st8
  refine ⟨s8, h8, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, initSt, a2]

end IpadAgent

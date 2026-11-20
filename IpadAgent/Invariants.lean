import IpadAgent.Reachability

/-!
### 4. 不变式证明

主要证明套路：对 `Reachable` 做归纳，再对最后一步 `Step` 分类讨论。
状态在不同迁移下如何变化，正是每个分支需要处理的内容。
-/
namespace IpadAgent

variable {hash : String → Digest}

/-- INV-1：未通过 SSH 配对，就不可能初始化沙箱。 -/
theorem provisioned_implies_paired {s : St} (h : Reachable hash s) :
    s.provisioned = true → s.paired = true := by
  induction h with
  | init => intro hs; simp [initSt] at hs
  | step _ hstep ih =>
      intro hs
      cases hstep with
      | sshAuth_ok _ => rfl
      | sshAuth_fail => exact ih hs
      | init_ok hp _ => exact hp
      | init_fail _ => exact ih hs
      | readLogs => exact ih hs
      | propose _ => exact ih hs
      | approve _ _ => exact ih hs
      | exec_ro _ _ _ _ _ => exact ih hs
      | exec_side _ _ _ _ _ _ => exact ih hs

/-- INV-2：一旦执行过命令，沙箱必已初始化。 -/
theorem exec_implies_provisioned {s : St} (h : Reachable hash s) :
    s.executed ≠ [] → s.provisioned = true := by
  induction h with
  | init => intro hne; simp [initSt] at hne
  | step _ hstep ih =>
      intro hne
      cases hstep with
      | sshAuth_ok _ => exact ih (by simpa using hne)
      | sshAuth_fail => exact ih (by simpa using hne)
      | init_ok _ _ => rfl
      | init_fail _ => exact ih (by simpa using hne)
      | readLogs => exact ih (by simpa using hne)
      | propose _ => exact ih (by simpa using hne)
      | approve _ _ => exact ih (by simpa using hne)
      | exec_ro _ _ hp _ _ => exact hp
      | exec_side _ _ hp _ _ _ => exact hp

/-- INV-3a：只读白名单在整个生命周期内固定，客户端改不了。 -/
theorem roAllow_fixed {s : St} (h : Reachable hash s) :
    s.roAllow = roToolBodies.map hash := by
  induction h with
  | init => rfl
  | step _ hstep ih =>
      cases hstep with
      | sshAuth_ok _ => exact ih
      | sshAuth_fail => exact ih
      | init_ok _ _ => exact ih
      | init_fail _ => exact ih
      | readLogs => exact ih
      | propose _ => exact ih
      | approve _ _ => exact ih
      | exec_ro _ _ _ _ _ => exact ih
      | exec_side _ _ _ _ _ _ => exact ih

/-- 审批列表中每条记录都满足摘要与内容的一致性。 -/
def ApprovedWF (hash : String → Digest) (s : St) : Prop :=
  ∀ a ∈ s.approved, a.digest = hash a.bytes

/-- 执行列表中每条记录都满足摘要与内容的一致性。 -/
def ExecutedWF (hash : String → Digest) (s : St) : Prop :=
  ∀ r ∈ s.executed, r.digest = hash r.bytes

/-- INV-3b：审批记录良构（摘要 = 该字节串的哈希）。 -/
theorem approved_wf {s : St} (h : Reachable hash s) : ApprovedWF hash s := by
  induction h with
  | init => intro a ha; simp [initSt] at ha
  | step _ hstep ih =>
      intro a ha
      cases hstep with
      | sshAuth_ok _ => exact ih a ha
      | sshAuth_fail => exact ih a ha
      | init_ok _ _ => exact ih a ha
      | init_fail _ => exact ih a ha
      | readLogs => exact ih a ha
      | propose _ => exact ih a ha
      | approve b n =>
          simp only [List.mem_cons] at ha
          rcases ha with hh | ha
          · subst hh; rfl
          · exact ih a ha
      | exec_ro _ _ _ _ _ => exact ih a ha
      | exec_side _ _ _ _ _ _ => exact ih a ha

/-- INV-3c：执行记录良构。 -/
theorem executed_wf {s : St} (h : Reachable hash s) : ExecutedWF hash s := by
  induction h with
  | init => intro r hr; simp [initSt] at hr
  | step _ hstep ih =>
      intro r hr
      cases hstep with
      | sshAuth_ok _ => exact ih r hr
      | sshAuth_fail => exact ih r hr
      | init_ok _ _ => exact ih r hr
      | init_fail _ => exact ih r hr
      | readLogs => exact ih r hr
      | propose _ => exact ih r hr
      | approve _ _ => exact ih r hr
      | exec_ro _ _ _ _ _ =>
          simp only [List.mem_cons] at hr
          rcases hr with hh | hr
          · subst hh; rfl
          · exact ih r hr
      | exec_side _ _ _ _ _ _ =>
          simp only [List.mem_cons] at hr
          rcases hr with hh | hr
          · subst hh; rfl
          · exact ih r hr

/--
INV-4（核心）：白名单之外的每一次执行，都对应一条 `(digest, nonce)` 相同的审批。
判定权在固定白名单上，不接受脚本自报的种类。
-/
theorem exec_approved_or_allowlisted {s : St} (h : Reachable hash s) :
    ∀ {r : Exec}, r ∈ s.executed →
      (∃ a ∈ s.approved, a.digest = r.digest ∧ a.nonce = r.nonce) ∨ r.digest ∈ s.roAllow := by
  induction h with
  | init => intro r hr; simp [initSt] at hr
  | step _ hstep ih =>
      intro r hr
      cases hstep with
      | sshAuth_ok _ => exact ih hr
      | sshAuth_fail => exact ih hr
      | init_ok _ _ => exact ih hr
      | init_fail _ => exact ih hr
      | readLogs => exact ih hr
      | propose _ => exact ih hr
      | approve b n =>
          rcases ih hr with ⟨a, ha, hd, hn⟩ | hro
          · exact Or.inl ⟨a, List.mem_cons_of_mem _ ha, hd, hn⟩
          · exact Or.inr hro
      | exec_ro sc n hp hro hf =>
          simp only [List.mem_cons] at hr
          rcases hr with hh | hr
          · subst hh
            exact Or.inr (by simpa using hro)
          · exact ih hr
      | exec_side sc n hp hnotro happr hf =>
          simp only [List.mem_cons] at hr
          rcases hr with hh | hr
          · subst hh
            exact Or.inl ⟨{ digest := hash sc.bytes, nonce := n, bytes := sc.bytes },
                          by simpa using happr, rfl, rfl⟩
          · exact ih hr

/-- INV-5：已执行 nonce 无重复（一次性、不可重放）。 -/
theorem nonce_nodup {s : St} (h : Reachable hash s) :
    (s.executed.map (fun r => r.nonce)).Nodup := by
  induction h with
  | init => simp [initSt]
  | step _ hstep ih =>
      cases hstep with
      | sshAuth_ok _ => exact ih
      | sshAuth_fail => exact ih
      | init_ok _ _ => exact ih
      | init_fail _ => exact ih
      | readLogs => exact ih
      | propose _ => exact ih
      | approve _ _ => exact ih
      | exec_ro sc n hp hro hf =>
          simp only [List.map_cons, List.nodup_cons]
          exact ⟨fun hmem => by
            obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmem
            exact hf r hr heq, ih⟩
      | exec_side sc n hp hnotro happr hf =>
          simp only [List.map_cons, List.nodup_cons]
          exact ⟨fun hmem => by
            obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmem
            exact hf r hr heq, ih⟩

/--
INV-6：哈希无碰撞 ⇒ 被执行的字节要么有等价审批，要么来自内置只读工具。
「日志注入」只能走审批路径。
-/
theorem bytes_binding (hinj : ∀ a b : String, hash a = hash b → a = b)
    {s : St} (h : Reachable hash s) :
    ∀ {r : Exec}, r ∈ s.executed →
      (∃ a ∈ s.approved, a.digest = r.digest ∧ a.nonce = r.nonce ∧ a.bytes = r.bytes) ∨
      ∃ b ∈ roToolBodies, b = r.bytes := by
  intro r hr
  rcases exec_approved_or_allowlisted h hr with ⟨a, ha, hd, hn⟩ | hro
  · have hA : a.digest = hash a.bytes := approved_wf h a ha
    have hE : r.digest = hash r.bytes := executed_wf h r hr
    exact Or.inl ⟨a, ha, hd, hn, hinj _ _ (by rw [← hA, hd, hE])⟩
  · rw [roAllow_fixed h] at hro
    obtain ⟨b, hb, hbeq⟩ := List.mem_map.mp hro
    have hE : r.digest = hash r.bytes := executed_wf h r hr
    exact Or.inr ⟨b, hb, hinj _ _ (by rw [hbeq, hE])⟩

/-- INV-7：读日志只写审计，不动任何状态。 -/
theorem readLogs_frame {s s' : St} (h : Step hash s .readLogs s') :
    s'.provisioned = s.provisioned ∧ s'.xrayRunning = s.xrayRunning ∧
    s'.roAllow = s.roAllow ∧ s'.approved = s.approved ∧ s'.executed = s.executed := by
  cases h
  simp

/-- INV-8：状态被改动 ⇒ 那次执行不在白名单内，且已有审批。 -/
theorem side_effect_requires_approval {s s' : St} {a : Act}
    (hstep : Step hash s a s') (hbefore : s.xrayRunning = false)
    (hafter : s'.xrayRunning = true) :
    ∃ (n : Nat) (sc : Script), a = Act.exec sc n ∧ hash sc.bytes ∉ s.roAllow ∧
      ({ digest := hash sc.bytes, nonce := n, bytes := sc.bytes } : Appr) ∈ s.approved := by
  cases hstep with
  | sshAuth_ok _ => simp [hbefore] at hafter
  | sshAuth_fail => simp [hbefore] at hafter
  | init_ok _ _ => simp [hbefore] at hafter
  | init_fail _ => simp [hbefore] at hafter
  | readLogs => simp [hbefore] at hafter
  | propose _ => simp [hbefore] at hafter
  | approve _ _ => simp [hbefore] at hafter
  | exec_ro sc n hp hro hf => simp [hbefore] at hafter
  | exec_side sc n hp hnotro happr hf => exact ⟨n, sc, rfl, hnotro, happr⟩

/-- INV-9：审计只前置追加，不可回改。 -/
theorem audit_append_only {s s' : St} {a : Act} (h : Step hash s a s') :
    ∃ e : String, s'.audit = e :: s.audit := by
  cases h <;> exact ⟨_, rfl⟩

end IpadAgent

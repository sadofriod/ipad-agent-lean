/-!
### 1. 数据模型

用结构体表示运行时数据，用 `St` 汇总系统状态。这里先不定义状态如何变化。
-/
namespace IpadAgent

abbrev Digest := Nat

/-- 脚本来源。`logTainted` 只作标注，不参与安全判定。 -/
inductive Prov where
  | user
  | agent
  | logTainted
  deriving DecidableEq, Repr

structure Script where
  bytes : String
  prov  : Prov
  deriving Repr

/-- 审批记录：iPad 对 `hash(bytes)` 的签名，并绑定 nonce。 -/
structure Appr where
  digest : Digest
  nonce  : Nat
  bytes  : String
  deriving Repr

/-- 执行记录。 -/
structure Exec where
  digest : Digest
  nonce  : Nat
  bytes  : String
  deriving Repr

/-- execd 内置的只读工具字节，初始化后固定。 -/
def roToolBodies : List String :=
  ["cat /var/log/xray/error.log | tail -n 200",
   "systemctl is-active xray",
   "xray run -test -c /usr/local/etc/xray/config.json"]

structure St where
  paired      : Bool := false
  provisioned : Bool := false
  xrayRunning : Bool := false
  roAllow     : List Digest := []
  approved    : List Appr := []
  executed    : List Exec := []
  audit       : List String := []
  deriving Repr

/-- 初始状态：只读白名单由内置工具字节的摘要构成。 -/
def initSt (hash : String → Digest) : St :=
  { roAllow := roToolBodies.map hash }

end IpadAgent

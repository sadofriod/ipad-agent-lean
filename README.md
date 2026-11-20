# IpadAgent Lean 导读

这是一个 Lean 4 状态机规格示例，用来练习代数数据类型、归纳关系和归纳证明。它描述 iPad 与 VPS 的脚本执行流程，不是实际 SSH 执行器，也不构成对真实系统安全性的证明。

## 阅读顺序

1. [IpadAgent/Model.lean](IpadAgent/Model.lean)：`inductive`、`structure` 和初始状态，回答“系统保存什么数据”。
2. [IpadAgent/Transition.lean](IpadAgent/Transition.lean)：`Act` 是请求的数据类型，`Step : St → Act → St → Prop` 是状态迁移关系；每个构造子是一条允许的迁移规则。
3. [IpadAgent/Reachability.lean](IpadAgent/Reachability.lean)：用归纳定义表示从初始状态重复执行迁移后能到达的状态。
4. [IpadAgent/Invariants.lean](IpadAgent/Invariants.lean)：对 `Reachable` 做 `induction`，再对最后一次 `Step` 做 `cases`，证明所有可达状态都满足的不变式。
5. [IpadAgent/Scenario.lean](IpadAgent/Scenario.lean)：手工构造每个中间状态与迁移证据，证明一个允许的完整场景确实可达。
6. [IpadAgent.lean](IpadAgent.lean)：统一导入模块，并用 `#print axioms` 检查定理依赖。

在证明中可以重点观察 `simp` 如何化简结构体更新，`rw` 如何替换等式，`rcases` 如何拆解存在量词与析取，以及 `exact` 如何把已有证据交给当前目标。

## 模型边界

以下是模型的假设或抽象，并非 Lean 定理证明出的现实保证：

- 哈希抗碰撞作为 `bytes_binding` 的参数 `hinj` 给出。
- 审批不可伪造被抽象成模型中只有 `approve` 迁移可以新增审批记录；没有建模真实签名算法或密钥。
- nonce 一次性由执行迁移的 `hfresh` 前置条件表达。
- 沙箱初始化前不能执行由 `provisioned` 前置条件表达；真实内核隔离能力不在模型内。
- 只读白名单来自内置固定字节，且状态迁移不提供修改白名单的规则；现实部署仍需保证实现与存储不可被客户端改写。
- `Prov.logTainted` 只记录来源，不参与安全决策。脚本是否只读由哈希是否命中白名单决定。

## 构建

安装 `lean-toolchain` 指定的 Lean 版本后，在仓库根目录运行：

```sh
lake build
```

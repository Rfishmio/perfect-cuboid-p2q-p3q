# 完美长方体 p²q、p³q 排除的形式化核查记录

**两条完美长方体非存在性定理均已在 Lean 4.34.1 与 Mathlib 4.34.1 下完成形式化证明。**

对任意不同素数 p、q，不存在体对角线为 p²q 或 p³q 的完美长方体。定理覆盖所有正整数棱长，包括棱长有公因子的情形。三条棱、三条面对角线和体对角线均用整数平方等式表达。

| 体对角线 | Lean 定理 |
| --- | --- |
| p²q | `CuboidFormal.forbidden_p2q` |
| p³q | `CuboidFormal.forbidden_p3q` |

`CuboidTheorems.lean` 给出两个最终定理。`CuboidAudit.lean` 用展开后的类型核对两条定理的原始陈述，并列出公理依赖。两条定理的公理依赖均为 `propext`、`Classical.choice` 和 `Quot.sound`。

```text
lake build CuboidProof
lake env lean CuboidAudit.lean
lake env leanchecker --fresh --verbose CuboidTheorems
```

## 已复跑的检查

| 文件 | 覆盖 | 结果 |
| --- | --- | --- |
| verify_arithmetic.py | 稀疏整数多项式逐系数比较、模 3/4/8/9 的完全枚举、赋值比较、素数大小矛盾、所有高斯指标与斜边角色的分支覆盖 | 203 项通过 |
| verify_b2_residues.py | p³q 的 B₂ 两个分支所用的模 16 与模 4 的有限蕴含，以及两条齐次恒等式 | 786,432 个模 16 元组及 1,536 个模 4 元组全部通过 |

七种 p²q 表示有 105 个无序三状态及斜边角色的组合。按证明使用的最小 p 进赋值条件，39 个组合需进一步处理。十种 p³q 表示同理有 360 个组合，66 个需进一步处理。精确检查程序核对了后续分支的覆盖。它们也独立重新展开了 p³q 中的判别式。有限余数枚举只针对局部等式的余数类，数学命题没有被改写成有限的素数搜索。

运行 `python run_checks.py`，日志为 `verification.log`。运行代码只依赖 Python 标准库。

## Lean 源码的范围

`lake build CuboidProof` 已成功构建全部二十个证明模块。最终定理调用的各项归约和分支前提均在同一工程中证明。

| 文件 | 已通过 Lean 检查的内容 |
| --- | --- |
| CuboidBasic.lean | 原始两个命题的统一表述、整数边长模型、恰有一个奇棱及两个偶棱的归约 |
| PrimitiveReduction.lean | 公因子缩放、本原情形的整除约束和低指数归约 |
| LowerDiagonal.lean | 素数幂与两不同素数乘积作为体对角线时的完整排除 |
| GaussianRepr.lean | 高斯整数范数、分解成两个有理素数的共轭高斯指数、单位与奇偶规范、七种和十种表示的有限展开 |
| GaussianPhase.lean | 共轭因子的互素性、分量非零及素数幂比较引理 |
| CuboidGaussian.lean、CuboidCandidates.lean、CuboidP2Candidates.lean | 从本原几何构造高斯数，将三个偶边及其勾股关系接入有限分类 |
| P2Core.lean、P2Data.lean、P2Phase.lean、P2Proof.lean | 数据构造、素数幂整除与七状态排除，得到本原 p²q 定理 |
| P3Core.lean | B₁ 分支的两个判别式、A₃ 的实部与 3 进分支 |
| P3Parity.lean | B₂ 分支的模 16/4 下降与符号分类 |
| P3Dispatch.lean、P3Data.lean、P3PairBridge.lean、P3MixedBridge.lean、P3Proof.lean | 十状态排除所需的高斯算术条件与完整分支归约，得到本原 p³q 定理 |
| CuboidTheorems.lean | 将本原排除、低指数排除与缩放归约接通，得到原始两条定理 |

## 环境记录

已在 Windows 上验证 `import Mathlib` 可以完整加载，并通过一个使用 `nlinarith` 的整数不等式。工程的 Lake 清单记录了 Mathlib 及其八个配套依赖的确切版本。

以前的两份数学证明放在 [p²q 证明说明](perfect_cuboid_p2q.md)和 [p³q 证明说明](perfect_cuboid_p3q.md)中。它们提供每个分支的数学接口。


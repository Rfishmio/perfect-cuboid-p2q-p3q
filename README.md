# 完美长方体体对角线的排除 · Perfect Cuboid Diagonals

对任意不同素数 \(p,q\)，完美长方体的体对角线既不能为 \(p^2q\)，也不能为 \(p^3q\)。两条定理覆盖所有正整数棱长，包括棱长有公因子的情形。

For distinct primes \(p,q\), neither \(p^2q\) nor \(p^3q\) can be the body diagonal of a perfect cuboid. Both theorems cover all positive integer edge lengths, including cuboids with a common edge divisor.

**作者 / Author** · GPT6.2  
**共同作者 / Co-authors** · 刘泰然 (Liu Tairan)、刘英玺 (Liu Yingxi)、朱禹丞 (Zhu Yucheng)、张利硕 (Zhang Lishuo)、孔维森 (Kong Weisen)

## 论文 / Papers

| 版本 / Edition | PDF | LaTeX |
| --- | --- | --- |
| 中文预印本 | [PDF](Perfect_Cuboid_p2q_p3q_Paper.pdf) | [源稿](Perfect_Cuboid_p2q_p3q_Paper.tex) |
| English preprint | [PDF](Perfect_Cuboid_p2q_p3q_Paper_EN.pdf) | [Source](Perfect_Cuboid_p2q_p3q_Paper_EN.tex) |

[中英文论文 ZIP / Bilingual paper ZIP](Perfect_Cuboid_p2q_p3q_Paper_Bilingual.zip) · [完整 Lean 验证 ZIP / Full Lean verification ZIP](Perfect_Cuboid_Lean_Full_Verification.zip)

## Lean 验证 / Lean verification

两条最终定理位于 [CuboidTheorems.lean](CuboidTheorems.lean)，分别为 `CuboidFormal.forbidden_p2q` 和 `CuboidFormal.forbidden_p3q`。

The project pins Lean 4.34.1 and Mathlib 4.34.1. With [Elan](https://github.com/leanprover/elan) installed, run the following commands from the repository root. / 安装 Elan 后，在仓库根目录运行以下命令。

```sh
lake build CuboidProof
lake env lean CuboidAudit.lean
lake env leanchecker --fresh --verbose CuboidTheorems
```

[CuboidAudit.lean](CuboidAudit.lean) checks the theorem statements and reports the axiom dependencies `propext`, `Classical.choice`, and `Quot.sound` for both theorems. Run `python run_checks.py` to repeat the supplementary arithmetic checks. / 审计文件核对定理陈述及公理依赖。辅助算术检查可通过同一目录下的 Python 脚本复跑。

[验证说明 / Verification notes](LEAN_VERIFICATION.md) · [构建日志 / Build log](lean-build.log) · [公理审计 / Axiom audit](lean-audit.log) · [内核重放 / Kernel replay](lean-replay.log) · [算术核查 / Arithmetic checks](verification.log)

两份早期数学证明随工程收录。[p²q 证明说明](perfect_cuboid_p2q.md) · [p³q 证明说明](perfect_cuboid_p3q.md)

The preprints give the detailed derivations, references, and acknowledgments. / 完整推导、参考文献和致谢见论文。

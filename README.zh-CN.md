# 辛球填充：中文导读

作者 Liang Song。版本 **1.2.0**。历次版本归档于总 DOI
[10.5281/zenodo.23756575](https://doi.org/10.5281/zenodo.23756575)（1.0.1 版 DOI 为
[10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498)）。
[英文说明与核验命令](README.md) · [四页总览导读 (PDF)](paper/overview/main.pdf) · [审阅指南](REVIEW.md) · [Epoch 问题专页](EPOCH.md)

## 一分钟理解

问题是：按辛几何的规则，把很多小球移进一个大球里。规则来自哈密顿动力学，要求运动保持辛结构，这比保持体积更严格。球在运动中可以变形，所以这不是日常的刚性堆球。

主结果：对**每一个整数 k ≥ 10（包含 k = 10, 11, 12, … 等全部非平方数）**以及**任意小的正体积缺口 0 < ε < 1**，同一个显式写出的全局光滑（`C^∞`）、空间紧支的哈密顿函数，在时间 1 把四维空间中 k 个闭单位球送进半径 `R = (k/(1−ε/4))^(1/4)` 的球，互不相交且体积占比恰好为 `1−ε/4`（论文 I）。更一般地，同一个显式构造覆盖四维中全部满足 `Σcᵢ² < C²`、`3cᵢ < C` 的填充（包含 **k ≥ 9** 个等球逼近满密度的显式哈密顿填充），并在 **2n ≥ 6** 维将体积不等式与 Gromov 两球不等式允许的全部填充实现为显式哈密顿流，同时给出输出“固定光滑截断 × 有理多项式”的一致停机算法（论文 II）。

Biran（1997）证明了四维 k ≥ 9 等球任意稠密填充的存在性。经典的显式满填充包括 Traynor 与 Schlenk 的平方数构造；其他构造方法包括折叠（folding）、缠绕（wrapping）、隧穿（tunnelling）、奇异辛曲线与极化构造以及近环面方法。据我们所知，本工作首次对每个非平方数 k ≥ 10 给出了将给定源球移至任意稠密填充的一致显式紧支光滑哈密顿函数（统一适用于全部 k ≥ 10 与任意正体积缺口），且构造与有限输出算法均不依赖 J-全纯曲线、Seiberg–Witten 理论或先前的填充存在性定理。

Lean 4 对具名哈密顿函数对照独立写出的规格做了完整检验：全局 `C^∞` 光滑、统一空间紧支撑、全局积分曲线存在，以及从**每个**源球内**每个**点出发的**每条**积分曲线在时间 1 都落入目标球；另有独立定理验证时间 1 映射的辛性与球像两两不交、有限输出算法的一致停机与正确性、定量 Picard–Lindelöf 轨迹证书，以及带初值与逐步状态扰动的定步长 RK4 一致落球定理（`epoch_rk4_convergence`，显式给出 `δ₀ = g/(4e^K)` 与 `N₀ = ⌈4Me^K/g⌉ + 1`）。

论文 I–II 解决了 [Epoch AI 辛球填充问题](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing) 的数学构造与可计算性部分，Lean 同时证明了上述定步长 RK4 收敛包含定理；构造一个同时满足已发布的 `float64` 接口、全局光滑要求与运行时限的提交仍是另一个独立的实现目标（详见 [EPOCH.md](EPOCH.md)）。`program/` 中的两个配套 Python 程序分别提供初等区域的快速定步长 RK4 实现与全参数闭式 `C⁴` 装填映射及精确逆映射验证。

## 四篇论文和两个正式程序

论文 I、II、IV 发展了 OpenAI 2026 年预印本（证明 2n ≥ 6 维填充存在性）的扭曲圆盘丛机制。四维部分的新机制包括：取代不动点迭代的线性比较恒等式（论文 I、IV）与标量比较数据（论文 II）、Fermat 三次曲线圆盘丛模型，以及避开无穷远直线的返回映射。在 2n ≥ 6 维，论文 II 将存在性证明中的每一步全部显式化。

| | 内容与正则性 | Lean |
|---|---|---|
| [论文 I](paper/p1/main.pdf)（四维等球，另有[补充材料](paper/p1/supplement.pdf)） | 对全部 k ≥ 10、ε ∈ (0, 1) 的全局 `C^∞` 紧支哈密顿主定理（最短完整路线）；对向量场扰动的显式稳定性裕度；带初值与逐步扰动的定步长 RK4 收敛包含推论（推论 D，`RK4Convergence.lean`） | 有 |
| [论文 II](paper/p2/main.pdf)（一般容量与高维，另有[补充材料](paper/p2/supplement.pdf)） | 同一个全局 `C^∞` 显式哈密顿函数处理所有合法数据：四维 Σcᵢ² < C²、3cᵢ < C（含不用全纯曲线与 SW 理论重证 Biran 的 k ≥ 9 满填充定理）；ℝ²ⁿ（n ≥ 3）满足体积与两球不等式的全部填充；输出有限多项式的一致停机算法 | 有 |
| [论文 III](paper/p3/main.pdf)（初等方法及其极限） | toric 与开窗构造：n(n+1) 个球放进 B(n+½)；每个 k 密度 ≥ 1 − 1/√k；10 个球密度 360/361。非平方 k 的格点和平衡剖面类密度障碍，以及 k = 10 的八满高柱锐界 | 无 |
| [论文 IV](paper/p4/main.pdf)（四维等球闭式辛填充） | 直接可求值的无 ODE 闭式 `C⁴` 辛装填映射、精确实数非成员认证逆映射 `Preimage`（§§2–7）、全参数 `(H0)–(H15)` 对任意 k ≥ 10、ε ∈ (0, 1) 的解析证明，以及由归一化原函数给出的径向 Alexander 生成元公式与抽象 ODE 轨迹证书（§8）；全局哈密顿提升仍未完成 | 抽象 ODE 引理；映射本身未形式化 |
| [程序](program/README.md) `solution_epoch.py` | 基于论文 III 初等构造的 PyTorch `float64` 哈密顿生成器：覆盖 k = 10（ε ≥ 0.005）、平方数（ε ≳ 0.002）及 k ≤ 10⁵ 的显式 `eps_min(k)` 以上，通过文档所列采样 RK4 包含测试（≤ 0.13 s/次哈密顿函数调用）；全局正则性与题目要求的 smooth 不同（球轨道外有角度分支射线，k = 10 含一处逐片 `C²` 窗口接缝） | 无 |
| [程序](program/README.md) `solution_embedding.py`（源码 [`embedding_src/`](program/embedding_src/)） | 实现论文 IV §§2–7 的闭式 `C⁴` 辛嵌入 `Embed(i, X)` 与无相消左逆 `Preimage(j, Y)`（非哈密顿 ODE）。实数算术下覆盖全部 k ≥ 10、ε ∈ (0, 1)；float64 下受条件数制约（见 [`program/README.md`](program/README.md)），配有 `check_embedding.py` 及基于 AST 变换的 100 位 `mpmath` 源码级复核（`check_embedding_mp.py`） | 无 |

## 覆盖范围与验证说明

- **四维填充范围**：覆盖全部满足 `Σcᵢ² < C²` 且 `3cᵢ < C` 的容量配置，包含任意 `k ≥ 9` 个等球逼近满密度的显式哈密顿填充（论文 I 给出 `k ≥ 10` 的线性比较直接路线，论文 II 覆盖 `k = 9` 与不等球容量锥）。
- **高维填充范围**：在 `2n ≥ 6` 维，将 OpenAI（2026）证明的 Siegel–Yao 体积与两球充要条件全部实现为显式哈密顿流。
- **正则性与形式化边界**：论文 I–II 的哈密顿函数全局 `C^∞` 并经 Lean 4 内核及新进程内核重放核验；论文 IV 的闭式装填映射为 `C⁴`；`RK4Convergence.lean` 中 `picard_lindelof_curve_unique` 仅需向量场 Lipschitz，而 `picard_lindelof_epoch_certificate` 假设 `H ∈ C^∞`。两个正式 Python 程序的复核日志见 [`program/README.md`](program/README.md)。

## 怎样少读就能判断

1. [`Problem.lean`](verification/Problem.lean)：问题的定义和假设，只依赖 Mathlib。
2. [`Statement.lean`](verification/Statement.lean) 与 [`RK4Convergence.lean`](verification/RK4Convergence.lean)：证明了哪些结论。
3. [审阅指南](REVIEW.md) 与 [Epoch 问题专页](EPOCH.md)：结论与四篇论文及程序的对应关系，以及各项自动检查的覆盖边界。

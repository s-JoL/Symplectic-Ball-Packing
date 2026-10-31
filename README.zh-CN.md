# 这个项目做了什么？

**Symplectic Ball Packing（辛球填充）**包含一篇数学论文、完整补充证明，以及 Lean 4 形式化证明。
作者为 Liang Song。英文论文标题是 *Explicit Hamiltonian ball packings in every dimension*。

版本 **1.0.1**，公开日期 **2026 年 10 月 29 日**。
DOI：[10.5281/zenodo.23763498](https://doi.org/10.5281/zenodo.23763498)。
[固定发布](https://github.com/s-JoL/Symplectic-Ball-Packing/releases/tag/v1.0.1) · [固定版本与存证核验](PROVENANCE.md)。

本次修正附录的两处论证及三处文档或注释，Lean 定义、定理陈述和证明未改动。
[修订说明](PROVENANCE.md#changes-from-100)列出具体更正；可选证明缓存和核验回执均更新为对应本版。

固定入口：[源码](https://github.com/s-JoL/Symplectic-Ball-Packing/tree/v1.0.1) · [审阅指南](https://github.com/s-JoL/Symplectic-Ball-Packing/blob/v1.0.1/REVIEW.md)。
原 [1.0.0 DOI 归档](https://doi.org/10.5281/zenodo.23756576)继续保留，原 GitHub Release 页面已移除。

[主论文](paper/main.pdf) · [补充材料](paper/supplement.pdf) · [专家审阅入口](REVIEW.md) · [英文说明与核验命令](README.md)

## 任意合法 k、ε 的完整参考程序

[`examples/packing.py`](examples/packing.py) 提供所有整数 `k≥10`、`0<ε<1`
的统一可执行算法，输出有限有理多项式乘固定光滑截断函数的全局 Hamiltonian。
[`verification/Executable.lean`](verification/Executable.lean) 核验实际可编译的
总定义，其返回值带有全部闭源球、实际时间一流和严格密度的完整证明。
ε、查询坐标和时间支持有效的可细化实数名；命令行直接接受精确有理字符串。
同一个输出函数提供严格值、完整梯度及实际 Hamiltonian 流的区间求值。

运行入口、全参数终止性、解释器对应论证与独立核验命令见
[`程序说明`](examples/PACKING.md)。该参考算法不设时间或资源上限，普通高密度
输入的穷举可能极其漫长。Python 求值器有数学对应论证和执行测试，尚无
Python 到 Lean 的形式化精化证明；没有声称通过 Epoch 接口、性能或官方验收。
这些程序内容在 v1.0.1 存证之后加入，不属于该已存证发布。

## 固定输入的程序示例

[`examples/k10.py`](examples/k10.py) 实现了固定 `k=10、ε=0.1` 的可执行程序，
提供一个全局标量 Hamiltonian，以及十个源球的解析轨迹求值。目标半径为 `73/40`，填充率大于 `0.9`。
运行方法、轨迹与 Hamilton 方程的关系及有限执行检查见 [`examples/README.md`](examples/README.md)。
这是固定输入的原生数值实现，尚未通过完整 Epoch AI 接口与性能验收，尚无 Python 到 Lean 的形式化精化证明。
这是 v1.0.1 存证之后的开发内容，不属于已存证的 v1.0.1 发布。

## 一分钟理解

可以把问题想成“按特定的几何规则，把很多小球移动到一个大球里”。这里的规则来自哈密顿动力学，
要求运动保持辛结构，比只保持体积更严格。球的像可以变形，所以它不是日常的刚性球堆积问题。

项目给出统一的运动构造：对任意整数 **k ≥ 10** 和 **0 < ε < 1**，从四维空间中相隔足够远的
k 个闭单位球出发，用一个光滑、空间支撑紧的哈密顿函数，在时间 1 把它们送进半径
`R = (k/(1−ε/4))^(1/4)` 的球里。它们互不相交，占据大球体积的比例恰好是 `1−ε/4`，因此可以任意接近填满。

已有的存在性结果告诉我们“这样的填充存在”。本工作的重点是给出一个明确的运动构造，并证明它
满足要求。项目还处理高维的一般容量数据，证明扰动稳定性，并证明一个有限输出算法会在所有合法输入上终止。

## 哪些边界不能混淆

一般容量定理均以 k ≥ 1、C > 0、每个 cᵢ > 0 为前提，并要求给定源球互不相交。

- 四维等球主定理的范围是 k ≥ 10；k ≥ 9 的等球填充稳定性是另一个推论。
- 一般四维不等球定理要求 `Σcᵢ² < C²` 和每个 `3cᵢ < C`；它没有声称解决所有四维不等球填充。
- 高维 ℝ²ⁿ、n ≥ 3 的定理要求体积不等式和两球不等式，还要求给定源球互不相交。
- “有限算法存在并终止”没有附带实用运行时间保证，也不等于已经提交并通过 Epoch 的 PyTorch 数值程序测试。
- Lean 核验的是文件中精确陈述的命题。人仍需要核对它与原数学问题是否一致。

## 怎么用很少的阅读判断做到了什么

先看英文 [审阅指南](REVIEW.md)，再对照：

1. [`Problem.lean`](verification/Problem.lean)：问题到底怎么定义，假设有哪些。
2. [`Statement.lean`](verification/Statement.lean)：最终到底证明了哪些结论。
3. [`Algorithm.lean`](verification/Algorithm.lean)：结论是否针对实际定义的构造。
4. 两个 computability 入口：算法的输入、输出、终止性和正确性分别是什么。

主论文讲构造路线；补充材料提供完整细节。[论文—Lean 索引](verification/PAPER-INDEX.md)可以定位
某个几何步骤的相关声明，不需要从头浏览全部代码。论文标签区分“完整陈述已验证”和“所需推论已验证”；后者只指构造所用的版本，
例如沿光滑族表述的返回映射拉回恒等式，不代表整段辅助陈述的所有结论或整个定义域都已形式化。

## 如何核验

按 [英文 README 的 Verify 部分](README.md#verify)操作。快速路径使用官方 Mathlib 缓存和项目的
可选编译缓存，再运行全部构建与审计。`scripts/check_kernel.sh` 用 Lean 自带的检查器，把编译后的
完整证明依赖重新送入新内核环境核验；从源代码重新构建则不使用项目缓存。三者的信任边界在审阅指南中分别说明。

## 给 AI 的阅读任务

可以把这个仓库交给 AI，并附上这段要求：

> 先读 README.md、REVIEW.md、verification/Problem.lean、verification/Statement.lean，
> 再按需要读两个 computability 入口和论文。请列出精确结论、全部输入假设、构造路线、前人工作、
> Lean 核验范围及未覆盖内容。请区分数学上的显式构造、可计算性定理、实用数值程序；区分缓存命中、
> 内核重放与源码重建。每项判断给出仓库文件或定理名，不把文字说明当作机器验证结果。

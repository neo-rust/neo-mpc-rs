# phase2 [![Crates.io](https://img.shields.io/crates/v/phase2.svg)](https://crates.io/crates/phase2) #

借鉴和模仿于伟大的ebfull的库[phase2](https://github.com/ebfull/phase2).

库正在开发过程中。



## 目的

本库是为参与NEO上零知识证明相关项目的开发者提供可信初始化过程以及基础电路的开发模板，简化开发过程。



## 基础使用流程

phase2过程需要多个贡献者提供不同的随机数种子来保证安全性，流程如下：

- 项目方或者开发者使用一个名为 phase1radix2mXX 的文件为自己的电路生成初始的Groth16 参数文件xxxx_phase2_paramter。phase1radix2mXX文件可以通过[powersoftau](https://github.com/doubiliu/powersoftau)生成，且文件规格需要与电路大小对应。
- 每一轮的贡献者使用秘密随机数更新上一轮贡献者提交的Groth16 参数文件xxxx_phase2_paramter，并公开提交新的Groth16 参数文件。其他参与者充当验证者的角色，验证新的Groth16 参数文件与上一轮贡献者提交的参数文件使用了相同的随机性。第一轮的贡献者使用项目方提供的初始Groth16 参数文件
- 直至最后一个贡献者更新完Groth16 参数文件，并被验证通过后，得到项目电路所需的安全Groth16 参数。



## Security Warnings

本库不对恒定时间操作、内存访问模式或抗侧信道攻击作出任何保证。

## License

根据以下任一许可
- Apache 许可证，版本 2.0，（[LICENSE-APACHE](LICENSE-APACHE) 或 http://www.apache.org/licenses/LICENSE-2.0）
- MIT 许可证（[LICENSE-MIT](LICENSE-MIT) 或 http://opensource.org/licenses/MIT）
  在你的选择。



## Contribution

除非您另有明确说明，否则任何有意做出的贡献
按照 Apache-2.0 中的定义，由您提交以包含在作品中
许可，应按上述双重许可，无任何附加条款或
条件。
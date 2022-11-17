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



## [Documentation](https://docs.rs/phase2/)

## Security Warnings

This library does not make any guarantees about constant-time operations, memory access patterns, or resistance to side-channel attacks.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

require("@parity/hardhat-polkadot");

/** @type import('hardhat/config').HardhatUserConfig */
module.exports = {
  solidity: {
    version: "0.8.28",
    settings: {
      optimizer: {
        enabled: true,
        runs: 200,
      },
      viaIR: true,
    },
  },
  // resolc: {
  //   compilerSource: "npm",
  //   settings: {
  //     optimizer: {
  //       enabled: true,
  //       fallbackOz: true,
  //     },
  //   },
  // },
  // resolc: {
  //   compilerSource: "binary",
  //   settings: {
  //     compilerPath:
  //       "/Users/tiago/Projects/test-hardhat-polkadot/resolc-universal-apple-darwin",
  //     optimizer: {
  //       enabled: true,
  //       fallbackOz: true,
  //     },
  //   },
  // },
  networks: {
    hardhat: {
      polkavm: false,
    },
  },
};

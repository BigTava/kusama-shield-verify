require("@parity/hardhat-polkadot");

/** @type import('hardhat/config').HardhatUserConfig */
module.exports = {
  solidity: {
    version: "0.8.28",
    settings: {
      optimizer: {
        enabled: true,
      },
    },
  },
  resolc: {
    compilerSource: "npm",
    settings: {
      optimizer: {
        enabled: true,
        fallbackOz: true,
      },
    },
  },
  networks: {
    hardhat: {
      polkavm: false,
    },
  },
};

require("@nomicfoundation/hardhat-ethers");
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
    passetHub: {
      polkavm: true,
      url: "https://testnet-passet-hub-eth-rpc.polkadot.io",
      accounts: [
        "271ad9a5e1e0178acebdb572f8755aac3463d863ddfc70e32e7d5eb0b334e687",
      ],
    },
  },
};

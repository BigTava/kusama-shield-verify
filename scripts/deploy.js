require("@nomicfoundation/hardhat-ethers");
const { ethers } = require("hardhat");

async function deploy() {
  const VerifierFactory = await ethers.getContractFactory("Halo2Verifier");
  const verifier = await VerifierFactory.deploy();

  console.log(`Halo2Verifier deployed to: ${verifier.address}`);
}

deploy()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });

import fs from "fs";

const EVM_ARTIFACT =
  "./artifacts/contracts/Verifiertogether.sol/Halo2Verifier.json";
const PVM_ARTIFACT =
  "./artifacts-pvm/contracts/Verifiertogether.sol/Halo2Verifier.json";

async function measureBytecode() {
  // EVM
  const evmArtifact = JSON.parse(fs.readFileSync(EVM_ARTIFACT, "utf8"));
  const evmBytecodeLength = evmArtifact.bytecode.length / 2;

  // PVM
  const pvmArtifact = JSON.parse(fs.readFileSync(PVM_ARTIFACT, "utf8"));
  const pvmBytecodeLength = pvmArtifact.bytecode.length / 2;

  const ratio = (pvmBytecodeLength / evmBytecodeLength).toFixed(2);

  console.log(`EVM bytecode: ${evmBytecodeLength} bytes`);
  console.log(`PVM bytecode: ${pvmBytecodeLength} bytes`);
  console.log(`PVM is ${ratio}x larger than EVM`);
}

measureBytecode()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });

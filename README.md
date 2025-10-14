# Master-final-thesis ZK-KYC-DSIG

## **ZK-KYC-DSIG: An eIDAS2 Compliant Privacy Preserving Identity Verification Framework via Zero Knowledge Proof and Digital Signature**

A detailed description of the project can be found in the docs folder.

---

## Requirements:

- **Operating System**: Windows 10 or later (this project uses Powershell scripts .ps1)
- **Circom**: Circom installed and usable globally
- **Node.js and npm**: LTS version
- **OpenSSL**: You need to have OpenSSL version 3 or higher installed (and the environment variables correctly set)
- **Other**: Set the Execution Policy of the OS in order to allow the usage of the Powershell scripts (.ps1)

## Getting Started

The order in which to call the commands for a linear execution are:

> npm run test:full

> npm run test:one

> npm run test:create

> npm run test:two

or

> npm run test:full

> npm run test:create

> npm run test:one

> npm run test:two

## Description of the commands

#### 1. Full Test

This command makes a complete run from compilation and setup of the zkp circuit until proof generation and verification.

> npm run test:full

**Note**: It is mandatory for the first time at least.

**Note**: It could require up to 30 hours and generate up to 20GB of data.

#### 2. Prove and Verify Tests

These commands run a simple prove generation and verification with 2 sets of data.

> npm run test:one

> npm run test:two

**Note**: Ensure the `/src/circuits/test_1/` and `/src/circuits/test_2/` folders exist before running tests. They are needed for the `test:one` and `test:two` commands.

**Note**: The `test:full` command: Compiles the circuit, Performs the setup, Generates the Solidity verifier, Generates the proof, Generates the witness, Verifies the proof and Creates a report.

**Note**: The `test:one` and `test:two` commands must be run after having run the `test:full` command at least once since they only do the following: Generate the witness, Generate the proof, Verify the proof and Create a report.

**Note**: The `test:two` command must be run only after having run the `test:create` command since it uses the crafted certificates generated with OpenSSL.

#### 3. Generating a local root CA certificate and signing with a user certificate

The following test will create a file with a user fiscal code, generate a CA certificate, generate a user certificate and sign the file.

> npm run test:create

**Note**: It refers to the data used for the command `npm run test:two`.

#### 4. Reports

All test runs will generate a report (in xml) format in the `reports` folder. **Please note** that every time a test is run, the report is overwritten.

#### 5. Testing the proof verification on chain

Run the following command in the build folder where all the zkp files have been generated.

> snarkjs generatecall

It will create the inputs for the contract call.

**Note**: The contract allow users to securely deposit ETH, verify their identity using ZK-SNARK proofs, check the verification status and withdraw ETH after a successful verification.

---

## Features

- **Privacy-Preserving**: No information of the user is disclosed.
- **Digital Signature**: Guarantees identity of the user as well as authenticity and integrity of the data.
- **eIDAS-2 Compliant**: Aligned with the EU regulations.
- **SSI Principles**: Aligned with the SSI principles.
- **Automated Testing**: Simple npm scripts for usage.

pragma circom 2.2.0;

include "@zk-email/circuits/lib/base64.circom";
include "@zk-email/circuits/lib/rsa.circom";
include "@zk-email/circuits/lib/sha.circom";
include "@zk-email/circuits/utils/array.circom";
include "@zk-email/circuits/utils/regex.circom";
include "@zk-email/circuits/utils/hash.circom";
include "@zk-email/circuits/utils/bytes.circom";
include "circomlib/circuits/bitify.circom";
include "./helpers/FormatterAndSignatureVerifier.circom";
include "./helpers/ExtractMessageDigestFromSignedAttributes.circom";
include "./helpers/VerifyHash.circom";
include "./helpers/VerifySimpleRsaEncryptionBase64AndExtractSubstring.circom";
include "./helpers/VerifyFiscalCodeAndPubkeyFromCertTbs.circom";

template ZkpKycDigSig(maxSignedAttributesLength, maxCertificateTbsLength, chunksBitLength, totalChunksNumber) {

    signal input SignedAttributes[maxSignedAttributesLength];
    signal input SignedAttributesLength;
    signal input Signature[totalChunksNumber];
    signal input PublicKeyModulus[totalChunksNumber];

    signal input CertificateTbs[maxCertificateTbsLength];
    signal input CertificateTbsLength;
    signal input CertificateSignature[totalChunksNumber];
    signal input CaPublicKeyModulus[totalChunksNumber];
    
    signal input JudgePublicKeyModulus[totalChunksNumber];

    //for extracting the message digest from the signed attributes
    signal input MessageDigestPatternStartingIndex;
    var maxMessageDigestLength = 32;

    //for extracting the fiscal code and the public key from the certificate tbs
    var maxFiscalCodeLength = 16;
    //signal input FiscalCodePatternStartingIndex;
    //signal input PublicKeyModulusPatternStartingIndex;

    //The content must be as long as the key so 2048 bits = 256 bytes
    var maxDecryptedContentLength = 256;
    //Value 344 is mandatory since it's the base64 length of an rsa 2048 signature
    var maxContentLength = 344;
    signal input Content[maxContentLength];
    signal input DecryptedContent[maxDecryptedContentLength];
    signal input DecryptedContentLength;
    signal input FiscalCodeIndexInDecryptedContent;

    //indexes to extract the fiscal code and the public key from the certificate tbs
    signal input FiscalCodePatternStartingIndexInTbs;
    signal input PublicKeyModulusPatternStartingIndexInTbs;
    

    //1-Verify the SIGNATURE of the signed attributes
    //2-Verify the SIGNATURE of the certificate
    component signatureVerify = FormatterAndSignatureVerifier(maxSignedAttributesLength,2048, chunksBitLength, totalChunksNumber);
    component certificateSignatureVerify= FormatterAndSignatureVerifier(maxCertificateTbsLength,2048, chunksBitLength, totalChunksNumber);

    signatureVerify.data <== SignedAttributes;
    signatureVerify.dataLength <== SignedAttributesLength;
    signatureVerify.signature <== Signature;
    signatureVerify.publicKey <== PublicKeyModulus;

    certificateSignatureVerify.data <== CertificateTbs;
    certificateSignatureVerify.dataLength <== CertificateTbsLength;
    certificateSignatureVerify.signature <== CertificateSignature;
    certificateSignatureVerify.publicKey <== CaPublicKeyModulus;

    //3-Verify the MESSAGE DIGEST from the signed attributes
    //Extract it
    component messageDigestExtractor = ExtractMessageDigestFromSignedAttributes(maxSignedAttributesLength, maxMessageDigestLength);
    messageDigestExtractor.SignedAttributes <== SignedAttributes;
    messageDigestExtractor.SignedAttributesLength <== SignedAttributesLength;
    messageDigestExtractor.MessageDigestPatternStartingIndex <== MessageDigestPatternStartingIndex;
    signal MessageDigest[maxMessageDigestLength] <== messageDigestExtractor.MessageDigest;

    //Verify it with the padded content
    component verifyHash = VerifyHash(maxContentLength);
    verifyHash.bytes <== Content;
    verifyHash.expectedSha <== MessageDigest;

    //4-Verify the CONTENT with the fiscal code and the judge public key
    component verifyRsa = VerifySimpleRsaEncryptionBase64AndExtractSubstring(maxDecryptedContentLength, maxContentLength, maxFiscalCodeLength, chunksBitLength, totalChunksNumber);
    verifyRsa.SignatureBase64 <== Content;
    verifyRsa.PublicKeyModulus <== JudgePublicKeyModulus;
    verifyRsa.Message <== DecryptedContent;
    verifyRsa.IndexOfPartialMessage <== FiscalCodeIndexInDecryptedContent;
    verifyRsa.MessageLength <== DecryptedContentLength;
    signal FiscalCode[maxFiscalCodeLength] <== verifyRsa.Substring;

    //5-Verify that the FISCAL CODE and the PUBLIC KEY corresponds with the ones contained in the CERTIFICATE TBS
    component verifyFiscalCodeAndPubKey = VerifyFiscalCodeAndPubkeyFromCertTbs(maxCertificateTbsLength,maxFiscalCodeLength,chunksBitLength,totalChunksNumber);
    verifyFiscalCodeAndPubKey.CertificateTbs <== CertificateTbs;
    verifyFiscalCodeAndPubKey.CertificateTbsLength <== CertificateTbsLength;
    verifyFiscalCodeAndPubKey.FiscalCode <== FiscalCode;
    verifyFiscalCodeAndPubKey.PublicKeyModulus <== PublicKeyModulus;
    verifyFiscalCodeAndPubKey.FiscalCodePatternStartingIndex <== FiscalCodePatternStartingIndexInTbs;
    verifyFiscalCodeAndPubKey.PublicKeyModulusPatternStartingIndex <== PublicKeyModulusPatternStartingIndexInTbs;
}

//The content is the ciphertext of a data structure containing the fiscal code encrypted with the judge public key
component main {public [CaPublicKeyModulus,JudgePublicKeyModulus,Content]}= ZkpKycDigSig(512,2048,121,17);
import Static from "./static";
import crypto from "crypto";
import forge from "node-forge";

export default class RSA extends Static {
  constructor() {
    super();
  }

  public static encrypt(pubkey: string, buffer: Buffer): string {
    const encrypted = crypto.publicEncrypt(
      {
        key: pubkey,
        padding: crypto.constants.RSA_NO_PADDING,
      },
      buffer
    );
    return encrypted.toString("base64");
  }

  public static decrypt(privkey: string, encryptedMessage: string): string {
    const buffer = Buffer.from(encryptedMessage, "base64");
    const decrypted = crypto.privateDecrypt(
      {
        key: privkey,
        padding: crypto.constants.RSA_NO_PADDING,
      },
      buffer
    );
    return decrypted.toString("utf8");
  }

  public static packMessage(salt: string, message: string): string {
    return JSON.stringify({ salt: salt, data: message });
  }

  public static packMessageAndPad(salt: string, message: string): Buffer {
    const raw = RSA.packMessage(salt, message);
    const messageBuffer = Buffer.from(raw, "ascii");

    const k = 256;
    const mLen = messageBuffer.length;

    //For deterministic PKCS#1 v1.5 padding, we use 11 bytes overhead:
    //0x00 | 0x02 | PS...PS | 0x00 | message
    if (mLen > k - 11) {
      throw new Error("Message too long to fit into 2048-bit RSA block with deterministic PKCS#1 v1.5 padding.");
    }
    //Build the PS (padding) region. For determinism: fill with 0x01
    const psLen = k - mLen - 3;
    const ps = Buffer.alloc(psLen, 0x01);

    //Build the final padded buffer:
    //0x00 0x02 [psLen bytes of 0x01] 0x00 [the message]
    const em = Buffer.concat([Buffer.from([0x00, 0x02]), ps, Buffer.from([0x00]), messageBuffer]);

    return em;
  }

  public static rsaRawEncrypt(message: Buffer, pubKeyPem: string): string {
    const publicKey = forge.pki.publicKeyFromPem(pubKeyPem) as forge.pki.rsa.PublicKey;

    const e = BigInt(publicKey.e.toString());
    const n = BigInt("0x" + publicKey.n.toString(16));

    const m = BigInt("0x" + message.toString("hex"));

    //c = m^e mod n
    const c: BigInt = m ** e % n;

    return Buffer.from(c.toString(16), "hex").toString("base64");
  }
}

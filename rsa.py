from sage.all import *
import os
import hashlib
from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric import rsa

def bytes_to_binary(byte_string):
    binary_string = ''.join(format(byte, '08b') for byte in byte_string)
    return binary_string

def binary_to_bytes(binary_string):
    bytes_array = bytearray(int(binary_string[i:i+8], 2) for i in range(0, len(binary_string), 8))
    return bytes(bytes_array)

def gen_prime(bits):
    return random_prime(2**(bits//2))

def gen_keys(bits):
    p = gen_prime(bits)
    q = gen_prime(bits)
    n = p * q
    phi = (p - 1) * (q - 1)

    e = ZZ.random_element(2, phi - 1)
    while gcd(e, phi) != 1:
        e = ZZ.random_element(2, phi - 1)

    d = power_mod(e, -1, phi)

    dmp1 = d % (p - 1)
    dmq1 = d % (q - 1)
    iqmp = pow(q, -1, p)

    cryptography_public_key = rsa.RSAPublicNumbers(int(e), int(n)).public_key(default_backend())
    cryptography_private_numbers = rsa.RSAPrivateNumbers(
        int(p),
        int(q),
        int(d),
        int(dmp1),
        int(dmq1),
        int(iqmp),
        public_numbers=cryptography_public_key.public_numbers()
    )
    cryptography_private_key = cryptography_private_numbers.private_key(default_backend())

    save_pem_key(cryptography_public_key, 'public_key.pem', 'public')
    save_pem_key(cryptography_private_key, 'private_key.pem', 'private')

    return ((n, e), (n, d))

def I2OSP(x, x_len):
    if x >= 256 ** x_len:
        raise OverflowError("integer too large")
    digits = []
    for _ in range(x_len):
        digits.append(x % 256)
        x //= 256
    return bytes(reversed(digits))

def OS2IP(x):
    return sum(b * 256 ** i for i, b in enumerate(x))

# Generating a mask for OAEP using SHA-256 hash function
def mgf(seed, length):
    t = b""
    for counter in range((length + hashlib.sha256().digest_size - 1) // hashlib.sha256().digest_size):
        c = I2OSP(counter, 4)  # Convert counter to a 4-byte string
        t += hashlib.sha256(seed + c).digest()
    return t[:length]

def add_oaep_padding(msg, n):
    k = (n.nbits() + 7) // 8

    # Calculating the hash length using SHA-256
    hlen = hashlib.sha256().digest_size

    max_length = k - 2 * hlen - 2

    if len(msg) > max_length:
        raise ValueError("Message too long for padding.")

    # Hashing empty string since L is not given
    lhash = hashlib.sha256(b'').digest() 

    # Calculating the padding string
    ps = b'\x00' * (k - len(msg) - 2 * hlen - 2)

    # Concatenating lhash, ps, 0x01, and the original message to form the data block (db)
    db = lhash + ps + b'\x01' + msg

    # Generating a random seed for masking
    seed = os.urandom(hlen)

    # Generating a mask for the data block (db)
    db_mask = mgf(seed, k - hlen - 1)

    # XOR the data block (db) with the mask to obtain masked_db
    masked_db = bytes(x ^ y for x, y in zip(db, db_mask))

    # Generating a mask for the seed
    seed_mask = mgf(masked_db, hlen)

    # XOR the seed with the seed mask to obtain masked_seed
    masked_seed = bytes(x ^ y for x, y in zip(seed, seed_mask))

    # Concatenating 0x00, masked_seed, and masked_db to form the final padded message
    padded_msg = b'\x00' + masked_seed + masked_db

    return padded_msg

def remove_oaep_padding(padded_msg, n):
    k = (n.nbits() + 7) // 8 
    hlen = hashlib.sha256().digest_size

    if len(padded_msg) != k or padded_msg[0] != 0x00:
        raise ValueError("Invalid padding length")

    # Extracting the masked seed and masked data block from the padded message
    masked_seed = padded_msg[1:1 + hlen]
    masked_db = padded_msg[1 + hlen:]

    # Generating a mask for the data block (masked_db)
    seed_mask = mgf(masked_db, hlen)
    seed = bytes(x ^ y for x, y in zip(masked_seed, seed_mask))

    # Generating a mask for the seed
    db_mask = mgf(seed, k - hlen - 1)

    # XOR the masked data block with the mask to obtain the original data block (db)
    db = bytes(x ^ y for x, y in zip(masked_db, db_mask))

    # Locate the position of the first 0x01 byte in the db
    sep_pos = db.find(b'\x01', hlen)

    # Check if the separator byte (0x01) is found at a valid position
    if sep_pos == -1 or sep_pos - hlen < 0:
        raise ValueError("Invalid padding")

    # Return the original data block starting from the position after the separator byte
    return db[sep_pos + 1:]

def encrypt(public_key, msg):
    n, e = public_key

    if len(msg) > ((n.nbits() + 7) // 8):
        raise ValueError("Message too long to encrypt.")

    padded_msg = add_oaep_padding(msg.encode(), n)
    binary_msg = bytes_to_binary(padded_msg)

    encrypted_msg = power_mod(int(binary_msg, 2), e, n)

    return encrypted_msg

def decrypt(private_key, encrypted_msg, bits):
    n, d = private_key

    decrypted_binary_msg = format(power_mod(encrypted_msg, d, n), '08b')

    decrypted_binary_msg = decrypted_binary_msg.zfill(bits)
    
    padded_msg = binary_to_bytes(decrypted_binary_msg)

    msg = remove_oaep_padding(padded_msg, n)

    return msg.decode()

def encrypt_message(public_key, msg):
    n, e = public_key

    k = (n.nbits() + 7) // 8
    hlen = hashlib.sha256().digest_size
    max_length = k - 2 * hlen - 2

    encrypted_msg = []

    if len(msg) > max_length:
        blocks = [msg[i:i + max_length] for i in range(0, len(msg), max_length)]

        for block in blocks:
            encrypted_block = encrypt(public_key, block)
            encrypted_msg.append(encrypted_block)

        return encrypted_msg

    else:
        encrypted_block = encrypt(public_key, msg)
        encrypted_msg.append(encrypted_block)

        return encrypted_msg

def decrypt_message(private_key, encrypted_msg, bits):
    decrypted_msg = []

    for block in encrypted_msg:
        decrypted_block = decrypt(private_key, block, bits)
        decrypted_msg.append(decrypted_block)

    return ''.join(decrypted_msg)

def save_pem_key(key, filename, key_type):
    if key_type == 'public':
        key_bytes = key.public_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PublicFormat.SubjectPublicKeyInfo,
        )
    elif key_type == 'private':
        key_bytes = key.private_bytes(
            encoding=serialization.Encoding.PEM,
            format=serialization.PrivateFormat.TraditionalOpenSSL,

            encryption_algorithm=serialization.NoEncryption()
        )
    else:
        raise ValueError("Invalid key type.")

    with open(filename, 'wb') as f:
        f.write(key_bytes)

def load_pem_key(filename, key_type):
    with open(filename, 'rb') as f:
        key_bytes = f.read()

    if key_type == 'public':
        loaded_key = serialization.load_pem_public_key(key_bytes, default_backend())
    elif key_type == 'private':
        loaded_key = serialization.load_pem_private_key(key_bytes, password=None, backend=default_backend())
    else:
        raise ValueError("Invalid key type.")

    return loaded_key

def get_key_components(key, key_type):
    if key_type == 'public':
        n = ZZ(key.public_numbers().n)
        e = ZZ(key.public_numbers().e)
        return n, e
    elif key_type == 'private':
        n = ZZ(key.private_numbers().p * key.private_numbers().q)
        d = ZZ(key.private_numbers().d)
        return n, d
    else:
        raise ValueError("Invalid key type.")

# Create keypair function

def get_keys(bits, new=False):
    if new:
        public_key, private_key = gen_keys(bits)
    else:
        load_public_key = load_pem_key('public_key.pem', 'public')
        load_private_key = load_pem_key('private_key.pem', 'private')

        public_key = get_key_components(load_public_key, 'public')
        private_key = get_key_components(load_private_key, 'private')

    return public_key, private_key

# Key size (bits)
# 128 bytes
bits = 1024

public_key, private_key = get_keys(bits, new=False)

message = "Small text test"
message2 = "Big text test: TestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTestTest"

print("Input message:", message, "\n")

encrypted_msg = encrypt_message(public_key, message)
print("Encrypted message:", encrypted_msg, "\n")

decrypted_msg = decrypt_message(private_key, encrypted_msg, bits)
print("Decrypted message:", decrypted_msg, "\n")

print("Input message:", message2, "\n")

encrypted_msg2 = encrypt_message(public_key, message2)
print("Encrypted message:", encrypted_msg, "\n")

decrypted_msg2 = decrypt_message(private_key, encrypted_msg2, bits)
print("Decrypted message:", decrypted_msg2)
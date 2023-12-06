from Crypto.PublicKey import ECC
from Crypto.Hash import SHA256
from Crypto.Signature import DSS
import time
import matplotlib.pyplot as plt
import csv

def generate_keys(n):
    """ Generate ECC key pairs for n participants """
    keys = [ECC.generate(curve='P-256') for _ in range(n)]
    return keys

def sign_message(hash_message, private_keys):
    """ Sign a hashed message with all private keys """
    signatures = [DSS.new(key, 'fips-186-3').sign(hash_message) for key in private_keys]
    return signatures

def verify_signatures(hash_message, signatures, public_keys):
    """ Verify all signatures against the public keys """
    for signature, public_key in zip(signatures, public_keys):
        try:
            verifier = DSS.new(public_key, 'fips-186-3')
            verifier.verify(hash_message, signature)
        except (ValueError, TypeError):
            return False
    return True

# Measurements
execution_times = []
participants_range = range(2, 101)

for n in participants_range:
    start_time = time.time()
    
    # Key generation
    keys = generate_keys(n)
    private_keys = [key for key in keys]
    public_keys = [key.public_key() for key in keys]

    # Signatures
    message = "example_message"
    hash_message = SHA256.new(message.encode())
    signatures = sign_message(hash_message, private_keys)

    # Verification
    try:
        verification_result = verify_signatures(hash_message, signatures, public_keys)
        if verification_result:
            print("Verification succeeded.")
        else:
            print("Verification failed.")
    except Exception as e:
        print(f"Verification failed with error: {e}")

    end_time = time.time()
    execution_times.append(end_time - start_time)

# Plotting
plt.plot(participants_range, execution_times)
plt.xlabel('party_number')
plt.ylabel('execution_time (sec)')
plt.title('ECDSA_n-out-of-n_threshold_signature')
plt.show()

# Saving to CSV
csv_filename = 'ecdsa_execution_times.csv'
with open(csv_filename, 'w', newline='') as file:
    writer = csv.writer(file)
    writer.writerow(['Number of Participants', 'Execution Time (s)'])
    for n, time in zip(participants_range, execution_times):
        writer.writerow([n, time])

csv_filename

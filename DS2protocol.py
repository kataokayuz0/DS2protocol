#Matrix generation
import hashlib
from sage.all import *
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler
from sage.modules.free_module_element import vector as sage_vector

# Parameters
number = 2 ** 46
next_prime_number = next_prime(number)
while next_prime_number % 8 != 5:
    next_prime_number = next_prime(next_prime_number)
q = next_prime_number
print(q)
n = 256
k, l = 2, 2
sigma = 3  # Standard deviation for Gaussian sampler
party_number = 2

# Define the ring Rq
R.<x> = PolynomialRing(ZZ)
Zq = Integers(q)
Rq = PolynomialRing(Zq, 'x').quotient(x^n + 1)

def discrete_gaussian_sampler(std_dev, ring):
    D = DiscreteGaussianDistributionIntegerSampler(sigma=std_dev)
    return ring([D() for _ in range(n)])

def commit(matrix, party_number):
    combined = str(matrix) + str(party_number)
    return hashlib.sha256(combined.encode()).hexdigest()

# H1 function representing the random oracle commitment
def H1(matrix, party_number):
    return commit(matrix, party_number)

# Generate k×l matrices using discrete Gaussian samplers
matrices = []
for _ in range(party_number):
    matrix = Matrix(Rq, k, l, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
    matrices.append(matrix)
    print(matrices)

# Commitments for each party
gn = []
for i, matrix in enumerate(matrices):
    commitment = H1(matrix, i + 1)
    gn.append(commitment)

print("Commitments stored in gn:", gn)

# 1. Upon receiving gj for all j ∈ [n − 1] send out An.
An = matrices
print("Sending out An:", An)

# 2. Upon receiving Aj for all j ∈ [n − 1]:
abort_flag = False
for j, Aj in enumerate(matrices[:-1]):
    if H1(Aj, j+1) != gn[j]:
        abort_flag = True
        break

if abort_flag:
    print("Sending out: abort")
else:
    A = sum(matrices)
    I = identity_matrix(Rq, k)
    A_bar = A.augment(I)
    print("Public random matrix A¯:\n", A_bar)
    
    
#Key Pair Generation
# H2 function representing the random oracle commitment
def H2(matrix, party_number):
    return commit(matrix, party_number)

# Parameters
eta = 5  # Bound for Sη

# Sη から l+k の大きさの要素をランダムに取り出す関数
def sample_from_S_eta(eta, size):
    return [ZZ.random_element(-eta, eta+1) for _ in range(size)]

# sn の初期化とデータの格納
sn = [sample_from_S_eta(eta, l+k) for _ in range(party_number)]
print(sn)

tn = [A_bar * vector(ZZ, s) for s in sn]
print(tn)

g_prime_n = H2(tn, party_number)
print("Sending out g'n:", g_prime_n)

# 2. Upon receiving g'j for all j ∈ [n − 1] send out tn.
print("Sending out tn:", tn)

# 3. Upon receiving tj for all j ∈ [n − 1]:
abort_flag = False
t_values = [tn]  # Assuming tn is already received

# Mock storage for g'j values (for the sake of this example)
g_prime_values = [g_prime_n]  # Assuming g_prime_n is already received

for j in range(party_number-1):  # Simulating the reception of other t values
    tj = [A_bar * vector(ZZ, s) for s in sn]
    t_values.append(tj)
    
    # Mock generation and storage of g'j values
    g_prime_j = H2(tj, j+1)
    g_prime_values.append(g_prime_j)
    
    if H2(tj, j+1) != g_prime_values[j+1]:  # Check against stored g'j values
        abort_flag = True
        break

if abort_flag:
    print("Sending out: abort")
else:
    t_combined = tuple(sum(t) for t in zip(*t_values))
    print("Combined public key t:", t_combined)

# Local output for Pn
skn = sn
pk = (A, t_combined)
#print("Local output for Pn (skn, pk):", skn, pk)
print("skn", skn)
print("pk", pk)


#Protocol DS2.sign(sid, skn, pk, μ))
#Inputs    

# H3 function for computing the per-message commitment key
def H3(message, public_key):
    combined = str(message) + str(public_key)
    return hashlib.sha256(combined.encode()).hexdigest()

# 1. Pn receives the inputs
sid = "unique_session_id_123"  # Example session ID
used_sids = set()  # Set to keep track of used session IDs
message = "example_message"

# 2. Pn verifies that sid has not been used before
if sid in used_sids:
    print("Session ID has been used before. Protocol not executed.")
else:
    used_sids.add(sid)
    
    # 3. Pn locally computes the per-message commitment key
    ck = H3(message, pk)
    print("Per-message commitment key ck:", ck)
    
    
    
#Signature Generation    
import random
from sage.modules.free_module_element import vector
# Parameters
eta = 5
k, l = 2, 2
N = 256
alpha = 2  # Example value for alpha
kappa = 60  # Example value for kappa
T = kappa * eta * sqrt(N * (l + k))
sigma = alpha * T
gamma = 1.1  # Example value for gamma
B = gamma * sigma * sqrt(N * (l + k))
t = 3
M = e^((t/alpha) + (1/(2*alpha^2)))
trapl, trapw = ceil(log(q, 2)), ceil(log(q, 2))
rn = []

# H0 function
def H0(com, message, public_key):
    combined = str(com) + str(message) + str(public_key)
    hashed = hashlib.sha256(combined.encode()).digest()
    return vector(ZZ, hashed)[:l+k]  # Convert the hash to a vector in R

# Commit function
def Commit(ck, msg, r=None):
    if r is None:  # If r is not provided, sample it from D(Sr)
        r = ZZ.random_element(-Sr, Sr + 1)
    combined = str(ck) + str(msg) + str(r)
    return hashlib.sha256(combined.encode()).hexdigest()

# Openck function
def Openck(Ahat, f1_f2, wn, r):
    Ahat_r = Ahat * r
    listzero = [Rq(0)]
    listwn = wn[i]
    matrix_zero = Matrix(Rq, [listzero])
    matrix_wn = Matrix(Rq, 1, 1, [listwn])
    zero_x = matrix_zero.stack(matrix_wn)
    if f1_f2 == Ahat_r + zero_x and r.norm()^2 <= B:
        return 1
    else:
        return 0
    
def polynomial_to_vector(poly, n):
    return vector(ZZ, [poly[i] for i in range(n)])

def convert_to_Rq_module(vec, Rq):
    return vector(Rq, [Rq(x) for x in vec])

def lift_ringelt_to_integervec(z):
    print('ztype', type(z)) 
    return vector(ZZ, [(a + q // 2).lift() - q // 2 for a in z])

Rm = vector([random.uniform(0, 1) for _ in range(l+k)])    
s = alpha * T * (sqrt(2 * pi))
    
def Ds(x, Rm, s):
    x_lifted = lift_ringelt_to_integervec(x)
    Rm_lifted = lift_ringelt_to_integervec(Rm)
    
    rohs_zn = exp((-pi * (x_lifted.norm()^2)^2) /  s^2)
    rohs_rm = exp((-pi * (Rm_lifted.norm()^2)^2) /  s^2)
    return rohs_zn / rohs_rm

def Dcsn_s(v, x, Rm, s):
    x_v_lifted = lift_ringelt_to_integervec(x-v)
    Rm_v_lifted = lift_ringelt_to_integervec(Rm-v)
    
    rohcsn_s_zn = exp((-pi * (x_v_lifted.norm()^2)^2) /  s^2)
    rohcsn_s_rm = exp((-pi * (Rm_v_lifted.norm()^2)^2) /  s^2)
    
    # ゼロ除算エラーを回避するための小さな値
    epsilon = 1e-10
    
    # 値を印刷してデバッグ
    print("rohcsn_s_rm:", rohcsn_s_rm)
    
    return rohcsn_s_zn / (rohcsn_s_rm + epsilon)


def rejection_sample(csn_list, zn_list):
    print("Starting rejection_sampling...")  # 追加
    
    csn_result = []
    zn_result = []
    for csn, zn in zip(csn_list, zn_list):
        csn_vec = vector(Rq, csn)
        zn_vec = vector(Rq, zn)
        print("zn", zn_vec)
        
        # 比率を計算
        ratio = Ds(zn_vec, Rm, s) / (M * Dcsn_s(csn_vec, zn_vec, Rm, s))

        # 比率と1の小さい方を選ぶ
        acceptance_probability = min(1, ratio)
        random_probability = random.random()
        print("acceptance_probability", acceptance_probability)
        print("random_probability", random_probability)

        # ランダムな確率を使用してサンプルを受け入れるか拒否するかを決定
        if random_probability >= acceptance_probability:
            return "restart"
        else:
            csn_result.append(csn_vec)
            zn_result.append(zn_vec)
            print(csn_result)
            print(zn_result)
            return (csn_result, zn_result)

# Signature Generation
def signature_generation(message, skn, pk, tn):
    z = []
    wjlist = []
    while True:
        print("Starting signature generation...")  # 追加

    # 1. Compute the first message
        print("Generating yn...")  # 追加

        # Generate k×l matrices using discrete Gaussian samplers
        yns = [vector(Rq, [discrete_gaussian_sampler(sigma, Rq) for _ in range(l+k)]) for _ in range(party_number)]
        print("yns", yns)

        print("Calculating wn...")  # 追加
        wn = []
        for i in range(party_number):
            wni = A_bar * yns[i]
            wn.append(wni)
        flat_wn = [item for sublist in wn for item in sublist]    
        print("wn", flat_wn)

        print("Commitck...")  # 追加

        #trapdoor commitment    
        comn = []
        #CGen
        for p in range(0, party_number*k):
            ahat1_1 = Matrix(Rq, 1, 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
            ahat1_j = Matrix(Rq, 1, trapl + 2*trapw - 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
            ahat2_j = Matrix(Rq, 1, trapl + 2*trapw - 2, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
            list1 = [Rq(0), Rq(1)]
            matrix_list1 = Matrix(Rq, [list1])
            matrix_up = ahat1_1.augment(ahat1_j)
            matrix_down = matrix_list1.augment(ahat2_j)
            Ahat = matrix_up.stack(matrix_down)
            #print(Ahat)
            #Commitck
            r = Matrix(Rq, trapl + 2*trapw, 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
            rn.append(r)
            fleft = Ahat * r
            listzero = [Rq(0)]
            listwn = flat_wn[p]
            print(listwn)
            matrix_zero = Matrix(Rq, [listzero])
            matrix_wn = Matrix(Rq, 1, 1, [listwn])
            fright = matrix_zero.stack(matrix_wn)
            f = fleft + fright
            comn.append(f)

        print("comn", comn)


    # 2.Upon receiving comj for all j ∈ [n − 1] compute the signature share as follows.   
        if abort_flag:
            return "abort"
        else:
            com_sum = sum(comn)
            c = H0(com_sum, message, pk)
            print("c", c)
            print("skn", skn)
            csn = [vector(Rq, [Rq(s * ci) for s, ci in zip(skn_row, c)]) for skn_row in skn]
            print("csn", csn)
            zn = [y + c for y, c in zip(yns, csn)]
            print("zn", zn)
            result = rejection_sample(csn, zn)
            if result == "restart":
                    print("Restarting the protocol inside signature generation...") 
                    continue  # 追加: "restart" が返された場合、ループの最初に戻る



    #3.Upon receiving restart from some party go to 1. Otherwise upon receiving (zj , rj ) for all j ∈ [n − 1] compute the combined signature as follows
        # a. For each j in [n-1], reconstruct wj and validate the signature share
        for j, zj in enumerate(zn):
            print(type(A_bar))
            print(type(zj))
            print(type(c))
            print(type(tn))
            zj = vector(Rq, zj)
            z.append(zj)
            print(type(zj))
            # Step 1: 各ポリノムをRqのベクトルに変換
            tn_vectors = [polynomial_to_vector(poly, n) for t in tn for poly in t]

            # Step 2: これらのベクトルを1つのリストに格納
            combined_list = [item for sublist in tn_vectors for item in sublist]

            # Step 3: リストをFreeModuleの要素として変換
            V = FreeModule(ZZ, len(combined_list))
            tn_vector = V(combined_list)
            print(type(tn_vector))
            c_tn_converted = convert_to_Rq_module(c * tn_vector[j], Rq)
            print("c_tn_converted", c_tn_converted)
            c_tn_converted_1 = vector(Rq, c_tn_converted[:party_number])
            c_tn_converted_2 = vector(Rq, c_tn_converted[party_number:])
            if j == 0:
                wj = A_bar * zj - c_tn_converted_1
                wjlist.append(wj)
                print("wj", wj)
            else:
                wj = A_bar * zj - c_tn_converted_2
                wjlist.append(wj)
                print("wj", wj)
            

        for i in range(party_number*k):
            # comn, rnから要素を取得
            comn_i = comn[i]
            rn_i = rn[i]
            wjlist_i = wjlist[i]

            # Openck のチェック
            if Openck(Ahat, comn_i, wjlist_i, rn_i) == 0:
                return "abort"

            # 追加の条件を確認
            if zj.norm()^2 > B:
                return "abort"

        # b. Compute z and r
        z = sum(z)
        r = sum(rn)

        # If the protocol does not abort, Pn obtains a signature (com, z, r) as local output
        return (com_sum, z, r)


        
# Example usage
while True:
    result = signature_generation(message, skn, pk, tn)
    if result == "abort":
        print("Protocol aborted.")
        break
    elif result == "restart":
        print("Restarting the protocol.")
        # Continue with the next iteration of the loop to restart the protocol
        continue
    else:
        com_sum, z, r = result
        print("Commitment com:", com_sum)
        print("Signature z:", z)
        print("Random value r:", r)
        break  # Successful completion, exit the loop
    
    
#Verification    
from sage.matrix.constructor import Matrix

# Verification Algorithm
def verification_algorithm(message, signature, pk):
    com_sum, z, r = signature
    A_bar, t_combined = pk
    
    # zをMatrix型に変換
    z_rows = []
    max_length = max(len(item) if isinstance(item, tuple) else 1 for item in z)
    for item in z:
        if isinstance(item, tuple):
            z_rows.append(list(item) + [Integer(0)]*(max_length - len(item)))
        else:
            z_rows.append([item] + [Integer(0)]*(max_length - 1))
    z_matrix = Matrix(z_rows)
    
    # t_combinedがMatrix型でない場合、Matrix型に変換（必要に応じて）
    if not isinstance(t_combined, Matrix):
        t_combined = Matrix(t_combined)
    
    ck = H3(message, pk)
    c = H0(com, message, pk)
    w = A_bar * z_matrix - c * t_combined
    if z_matrix.norm(2) <= Bn and Openck(ck, com, r, w) == 1:
        return True
    else:
        return False

# Example usage
message = "example_message"  # Sample message for testing
signature = (com, z, r)  # Sample signature from the provided signature algorithm output

result = verification_algorithm(message, signature, pk)
print(result)

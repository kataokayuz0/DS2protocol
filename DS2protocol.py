#Matrix Generation
import hashlib
import itertools
from sage.all import *
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler
from sage.modules.free_module_element import vector as sage_vector
​
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
​
# Define the ring Rq
R.<x> = PolynomialRing(ZZ)
Zq = Integers(q)
Rq = PolynomialRing(Zq, 'x').quotient(x^n + 1)
​
​
#グローバル変数にする
D = DiscreteGaussianDistributionIntegerSampler(sigma=sigma)
def discrete_gaussian_sampler(std_dev, ring):
    return ring([D() for _ in range(n)])
​
def commit(matrix, party_number):
    combined = str(matrix) + str(party_number)
    return hashlib.sha256(combined.encode()).hexdigest()
​
# H1 function representing the random oracle commitment
def H1(matrix, party_number):
    return commit(matrix, party_number)
​
# Generate k×l matrices using discrete Gaussian samplers
matrices = []
for _ in range(party_number):
    matrix = Matrix(Rq, k, l, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
    matrices.append(matrix)
    print(matrices)
​
# Commitments for each party
gn = []
for i, matrix in enumerate(matrices):
    commitment = H1(matrix, i + 1)
    gn.append(commitment)
​
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

# Sη から要素をランダムに取り出す関数
def sample_from_S_eta(eta, size):
    return [ZZ.random_element(-eta, eta+1) for _ in range(size)]

# sn の初期化とデータの格納
sn = [sample_from_S_eta(eta, l+k) for _ in range(party_number)]
print(sn)

tn = [A_bar * vector(ZZ, s) for s in sn]
print(tn)

g_prime_n = []
for i in range(party_number):
    g_prime_n_element = H2(tn[i], i)
    g_prime_n.append(g_prime_n_element)
print("Sending out g'n:", g_prime_n)

# 2. Upon receiving g'j for all j ∈ [n − 1] send out tn.
print("Sending out tn:", tn)

# 3. Upon receiving tj for all j ∈ [n − 1]:
abort_flag = False
t_values = tn  # Assuming tn is already received

# Mock storage for g'j values (for the sake of this example)
g_prime_values = g_prime_n  # Assuming g_prime_n is already received

for j in range(party_number):  # Simulating the reception of other t values
#         print('t_values[j]', t_values[j])
#         print('H2(t_values[j], j)', H2(t_values[j], j))
        if H2(t_values[j], j) != g_prime_values[j]:  # Check against stored g'j values
            abort_flag = True
            break

if abort_flag:
    print("Sending out: abort")
else:
    t_combined = sum(t_values)
    print("Combined public key t:", t_combined)

# Local output for Pn
skn = sn
pk = (A, t_combined)
#print("Local output for Pn (skn, pk):", skn, pk)
print("skn", skn)
print("pk", pk)    



#Protocol DS2.Signn(sid, skn, pk, µ)
#Inputs

# H3 function for computing the per-message commitment key
def H3(message, public_key, ck_limit):
    combined = str(message) + str(public_key)
    hash_output = hashlib.sha256(combined.encode()).hexdigest()
    hash_int = int(hash_output, 16)
    scale_factor = (2 * ck_limit) / (2**256 - 1)
    scaled_value = (hash_int * scale_factor) - ck_limit
    return scaled_value

# 1. Pn receives the inputs
sid = "unique_session_id_123"  # Example session ID
used_sids = set()  # Set to keep track of used session IDs
message = "example_message"

ck_limit = 5  # ckの最大値を示します。

# 2. Pn verifies that sid has not been used before
if sid in used_sids:
    print("Session ID has been used before. Protocol not executed.")
else:
    used_sids.add(sid)
    
    # 3. Pn locally computes the per-message commitment key
    ck = H3(message, pk, ck_limit)
    print("Per-message commitment key ck:", ck)
    
    
    
#Signature Generation
#Setting parameters

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
epsilon = 0.1
trapq_candidate = N ** (2 + epsilon)
trapq = next_prime(ceil(trapq_candidate)) #ceilを使って整数に丸める
trapl, trapw = ceil(log(trapq, 2)), ceil(log(trapq, 2))
s = alpha * T * (sqrt(2 * pi))



#1.Compute the first message as follows
#2. Upon receiving comj, compute the signature share

import random
from sage.modules.free_module_element import vector

# 可逆であることを確認する関数を定義
def is_invertible(m, Rq):
    try:
        _ = m.inverse()
        return True
    except:
        return False

# 可逆な行列を生成する関数を定義
def generate_invertible_matrix(sigma, Rq):
    while True:
        # ランダムな1x1行列を生成
        ahat1_1 = Matrix(Rq, 1, 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
        # その行列が可逆であるかを確認
        if is_invertible(ahat1_1, Rq):
            return ahat1_1  # 可逆ならこれを返す

def polynomial_to_vector(poly, N):
    # 多項式の係数をリストとして取得
    coeffs = poly.list()

    # N次までの係数を含むベクトルを作成
    # 多項式の次数がN未満の場合、残りの係数は0で埋める
    vec = vector([coeffs[i] if i < len(coeffs) else 0 for i in range(N)])

    return vec

def convert_to_Rq_module(vec, Rq):
    return vector(Rq, [Rq(x) for x in vec])

def lift_ringelt_to_integervec(z):
    print('ztype', type(z)) 
    return vector(ZZ, [(a + q // 2).lift() - q // 2 for a in z])

def lift_ringeltvec_to_integervec(z):
    chain_result = list(itertools.chain(*[lift_ringelt_to_integervec(xi) for xi in z]))
    print('chain_result', chain_result)
    return vector(ZZ, chain_result)        

def calculate_sums(csn_list, zn_list, s):
    rohs_rm_total = 0
    rohcsn_s_rm_total = 0

    for csn, zn in zip(csn_list, zn_list):
        # zn と csn が整数リストとして渡されることを想定しています
        # csn と zn をリフトしてから計算する必要があります
        zn_lifted = lift_ringeltvec_to_integervec(zn)
        csn_lifted = lift_ringeltvec_to_integervec(csn)
        rohs_rm_total += exp(-pi * (zn_lifted.norm()) / s^2)
        rohcsn_s_rm_total += exp(-pi * (csn_lifted.norm()) / s^2)

    return rohs_rm_total, rohcsn_s_rm_total

def Ds(x, s, rohs_rm):
    x_lifted = lift_ringeltvec_to_integervec(x)
    print('x_lifted', x_lifted)
    
    rohs_zn = exp(-pi * (x_lifted.norm()) /  s^2)
    print('rohs_zntype', type(rohs_zn))
    print('rohs_zn', rohs_zn)
    return rohs_zn / rohs_rm

def Dcsn_s(v, x, s, rohcsn_s_rm):
    x_v_lifted = lift_ringeltvec_to_integervec(x-v)
    print('x_v_lifted', x_v_lifted)
    rohcsn_s_zn = exp(-pi * (x_v_lifted.norm()) /  s^2)
    print('rohcsn_s_zn', rohcsn_s_zn)
    return rohcsn_s_zn / rohcsn_s_rm

#a. sample yn and compute wn
def sampleyn():
    sample_yn = [vector(Rq, [discrete_gaussian_sampler(sigma, Rq) for _ in range(l+k)]) for _ in range(party_number)]
    return sample_yn

def computewn(A_bar, sampled_yn):
    wn = []
    for i in range(party_number):
            wni = A_bar * sampled_yn[i]
            wn.append(wni)
    flat_wn = [item for sublist in wn for item in sublist]  
    return flat_wn

#b. compute comn with rn

def samplern():
    sampled_rn = []
    for i in range(0, party_number*k):
        r = Matrix(Rq, trapl + 2*trapw, 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
        sampled_rn.append(r) 
    return sampled_rn

def CGen():
    ahat1_1 = generate_invertible_matrix(sigma, Rq)
    ahat1_j = Matrix(Rq, 1, trapl + 2*trapw - 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
    ahat2_j = Matrix(Rq, 1, trapl + 2*trapw - 2, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
    list1 = [Rq(0), Rq(1)]
    matrix_list1 = Matrix(Rq, [list1])
    matrix_up = ahat1_1.augment(ahat1_j)
    matrix_down = matrix_list1.augment(ahat2_j)
    Ahat = matrix_up.stack(matrix_down)
    return Ahat    

def commitck(flat_wn, sampled_rn, Ahat):
    #Initialize commiment of each party
    comn_per_party = [[] for _ in range(party_number)]
    for p in range(0, party_number * k): # それぞれの係数に行うため、party_number * k回必要
        fleft = Ahat * sampled_rn[p]
        listzero = [Rq(0)]
        listwn = [flat_wn[p]] # 順に係数を取り出す
        print('listwn', listwn)
        matrix_zero = Matrix(Rq, [listzero])
        matrix_wn = Matrix(Rq, 1, 1, [listwn])
        fright = matrix_zero.stack(matrix_wn)
        f = fleft + fright
        #パーティごとのサブリストに追加
        comn_per_party[p // k].append(f)
    return matrix_zero, comn_per_party

def sum_commitments(commitments_per_party):
    return [sum(commitments) for commitments in zip(*commitments_per_party)]
    
#a. set com
def setcom(comn_per_party):
    com = sum_commitments(comn_per_party)
    return com

#b. derive challenge
# SHAKE関数を用いてランダムなビット列を生成する関数
def generate_random_bits(com, message, pk, length):
    seed = str(com) + str(message) + str(pk)
    shake = hashlib.shake_256()
    shake.update(seed.encode())
    return shake.digest(length)

# 1または-1の値をkappa個生成
def generate_coefficients(com, message, pk):
    random_bits = generate_random_bits(com, message, pk, kappa)
    coefficients = [1 if bit % 2 == 0 else -1 for bit in random_bits]
    return coefficients

# R上の多項式に係数をランダムに配置
def create_random_polynomial(com, message, pk, N, kappa):
    R = PolynomialRing(ZZ, 'x')
    x = R.gen()

    # kappa 個の位置をランダムに選択
    positions = random.sample(range(N), kappa)

    # 選択された位置に 1 または -1 をランダムに配置
    coefficients = generate_coefficients(com, message, pk)
    challenge = sum(random.choice([-1, 1]) * x^pos for pos in positions)

    # 係数が配置されていない位置には 0 を配置
    challenge += sum(0 * x^i for i in range(N) if i not in positions)

    print('challenge', challenge)
    return challenge

#c. Computes a signature share
def computezn(challenge, skn, yn):
    csn = [[challenge * element for element in row] for row in skn]
    csn = [vector(Rq, [Rq(x) for x in row]) for row in csn]
    computed_zn = [csn_elem + yn_elem for csn_elem, yn_elem in zip(csn, yn)]
    return computed_zn, csn

#d. Run the rejection sampling
def rejection_sample(csn_list, zn_list):
    print("Starting rejection_sampling...")  # 追加
    rejec_zn_result = []
    rohs_rm, rohcsn_s_rm = calculate_sums(csn_list, zn_list, s)
    for csn, zn in zip(csn_list, zn_list):
        print('aaaaaaa')
        csn_vec = vector(Rq, csn)
        zn_vec = vector(Rq, zn)

        # 比率を計算
        ratio = Ds(zn_vec, s, rohcsn_s_rm) / (M * Dcsn_s(csn_vec, zn_vec, s, rohcsn_s_rm))

        # 比率と1の小さい方を選ぶ
        acceptance_probability = min(1, ratio)
        random_probability = random.random()
        print("acceptance_probability", acceptance_probability)
        print("random_probability", random_probability)

        # ランダムな確率を使用してサンプルを受け入れるか拒否するかを決定
        if random_probability >= acceptance_probability:
            return "restart"
        else:
            rejec_zn_result.append(zn_vec)
    return rejec_zn_result
        
def sig1_sig2():
    while True:
        zn_result = []
        sampled_yn = sampleyn()
        flat_wn = computewn(A_bar, sampled_yn)
        sampled_rn = samplern()    
        Ahat = CGen()    
        matrix_zero, comn_per_party = commitck(flat_wn, sampled_rn, Ahat)
        com = setcom(comn_per_party)

        #send out comn        

        derived_challenge = create_random_polynomial(com, message, pk, N, kappa)
        computed_zn, csn = computezn(derived_challenge, skn, sampled_yn)
        result = rejection_sample(csn, computed_zn)
        if result == "restart":
            print("Restarting the protocol inside signature generation...") 
            continue
        else:
            zn_result = result
            print('zn_result', zn_result)
            break

    return Ahat, comn_per_party, matrix_zero, derived_challenge, sampled_rn, zn_result
            
Ahat, comn_per_party, matrix_zero, derived_challenge, sampled_rn, zn_result = sig1_sig2()           
print(len(sampled_rn))
print(len(zn_result))


#3. Upon receiving restart, go to 1. Otherwise upon receiving (zj, rj) compute the combined signature

# a. For each j in [n-1], reconstruct wj and validate the signature share
def recon_wj(A_bar, zn_result, challenge, tn):
#     challenge_coeffs = [challenge.coefficient(i) for i in range(N)] 
    reconted_wj = []
    for i in range(0, party_number):
        recon_wn_left_vector = A_bar * zn_result[i]
        recon_wn_right_vector = challenge * tn[i]
        recon_wn_left = Matrix(recon_wn_left_vector).transpose()
        recon_wn_right = Matrix(recon_wn_right_vector).transpose()
        print(type(recon_wn_left), type(recon_wn_right))
        reconted_wj.append(recon_wn_left - recon_wn_right)
    return reconted_wj

def validate_zn(zn_result):
    for i in range(0, party_number):
        zn_result_lifted = lift_ringeltvec_to_integervec(zn_result[i])
        zn_result_lifted_norm = zn_result_lifted.norm()
        print('zn_result_lifted_norm', zn_result_lifted_norm)
        if zn_result_lifted_norm > B:
            return "abort"
        
def validate_openck(sampled_rn, reconted_wj, matrix_zero, comn_per_party):
    print('a')
    flat_comn_per_party = [item for sublist in comn_per_party for item in sublist]
    for i in range(party_number*k):
        print('b')
        openck_fleft = Ahat * sampled_rn[i]
        print('d')
        openck_matrix_wn = Matrix(Rq, 1, 1, reconted_wj[i])
        print('e')
        openck_zero_x = matrix_zero.stack(openck_matrix_wn)
        print('f')
        openck_result = openck_fleft + openck_zero_x
        print('g')
        sampled_rn_lifted = lift_ringeltvec_to_integervec(sampled_rn[i])
        if flat_comn_per_party[i] == openck_result and sampled_rn_lifted.norm() <= B:
            return 1
        else:
            return "abort"
            break
            
#b. compute z  and r
def compute_signature(zn_result, sampled_rn):
    sign_zn = sum(zn_result)
    sign_rn = sum(sampled_rn)
    return (sign_zn, sign_rn)

reconted_wj = recon_wj(A_bar, zn_result, derived_challenge, tn)
print('reconted_wj', reconted_wj)
print('rows', reconted_wj.nrows(), 'cols', reconted_wj.ncols())


if validate_zn(zn_result) == "abort":
    print("protocol aborted.")
elif validate_openck(sampled_rn, reconted_wj, matrix_zero, comn_per_party) == "abort":
    print("protocol aborted.")
else:
    sign_zn, sign_rn = compute_singnature(zn_result, sampled_rn)
    print('sign_zn', sign_zn)
    print('sign_rn', sign_rn)
    
    
    
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

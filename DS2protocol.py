#DS2 protocol

#Matrix Generation
import hashlib
import itertools
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


#グローバル変数にする
D = DiscreteGaussianDistributionIntegerSampler(sigma=sigma)
def discrete_gaussian_sampler(std_dev, ring):
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



#Protocol DS2sign
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
epsilon = 0.1
trapq_candidate = N ** (2 + epsilon)
trapq = next_prime(ceil(trapq_candidate)) #ceilを使って整数に丸める
trapl, trapw = ceil(log(trapq, 2)), ceil(log(trapq, 2))

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

def H0(com, message, public_key):
    combined = str(com) + str(message) + str(public_key)
    hashed = hashlib.sha256(combined.encode()).digest()
    
    # ハッシュ値を1つの整数に変換
    hashed_integer = int.from_bytes(hashed, 'big')

    # 絶対値が1になるように調整
    scaled_integer = 1 if hashed_integer % 2 == 0 else -1

    # L1ノルムがkappaになるように調整
    final_value = scaled_integer * kappa

    return final_value

# Commit function
def Commit(ck, msg, r=None):
    if r is None:  # If r is not provided, sample it from D(Sr)
        r = ZZ.random_element(-Sr, Sr + 1)
    combined = str(ck) + str(msg) + str(r)
    return hashlib.sha256(combined.encode()).hexdigest()

# 全てのパーティのコミットメントを合計する関数
def sum_commitments(commitments_per_party):
    # zip(*commitments_per_party)は各サブリストから同じ位置にある要素を組み合わせる
    # すべての組み合わせた要素（つまり、各パーティの同じ位置にあるコミットメント）を足し合わせる
    return [sum(commitments) for commitments in zip(*commitments_per_party)]

# Openck function
def Openck(Ahat, f1_f2, wn, r):
    openck_Ahat_r = Ahat * r
    openck_listzero = [Rq(0)]
    openck_listwn = [wn]
    print('listwn', openck_listwn)
    openck_matrix_zero = Matrix(Rq, [openck_listzero])
    openck_matrix_wn = Matrix(Rq, 1, 1, [openck_listwn])
    openck_zero_x = openck_matrix_zero.stack(openck_matrix_wn)
    openck_result = openck_Ahat_r + openck_zero_x
    print('f1_f2', f1_f2)
    print('openck_result', openck_result)
    #r_lifted = lift_ringeltvec_to_integervec(r)
    if f1_f2 == openck_result:
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

def lift_ringeltvec_to_integervec(z):
    chain_result = list(itertools.chain(*[lift_ringelt_to_integervec(xi) for xi in z]))
    print('chain_result', chain_result)
    return vector(ZZ, chain_result)

s = alpha * T * (sqrt(2 * pi))

# def rohs_rm_cal(zn_list, s):
#     rohs_rm = 0
#     for zn in zn_list:
#         zn_list = vector(Rq, zn_list)
#         zn_list_lifted = lift_ringeltvec_to_integervec(zn_list)
#         rohs_zn = exp(-pi * (zn_list_lifted.norm()^2) /  s^2)
#         rohs_rm = rohs_rm + rohs_zn
#     return rohs_rm    

# def rohcsn_s_rm_cal(zn_list, csn_list, s):
#     rohcsn_s_rm = 0
#     for zn, csn in zip(zn_list, csn_list):
#         zn_list = vector(Rq, zn_list)
#         csn_list = vector(Rq, csn_list)
#         zn_v_lifted = lift_ringeltvec_to_integervec(zn_list - csn_list)
#         rohcsn_s_zn = exp(-pi * (zn_v_lifted.norm()^2) /  s^2)
#         rohcsn_s_rm = rohs_rm + rohs_zn
#     return rohcsn_s_rm

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


def rejection_sample(csn_list, zn_list):
    print("Starting rejection_sampling...")  # 追加
    
    rohs_rm, rohcsn_s_rm = calculate_sums(csn_list, zn_list, s)
    csn_result = []
    zn_result = []
    for csn, zn in zip(csn_list, zn_list):
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
            csn_result.append(csn_vec)
            zn_result.append(zn_vec)
            print(csn_result)
            print(zn_result)
            return (csn_result, zn_result)

# Signature Generation
def signature_generation(message, skn, pk, tn):
    global flat_wn
    global rn
    z = []
    wjlist = []
    while True:
        print("Starting signature generation...")  # 追加
        rn = []

    # 1. Compute the first message
        print("Generating yn...")  # 追加

        # Generate list using discrete Gaussian samplers
        yn = [vector(Rq, [discrete_gaussian_sampler(sigma, Rq) for _ in range(l+k)]) for _ in range(party_number)]
        print("yn", yn)

        print("Calculating wn...")  # 追加
        wn = []
        for i in range(party_number):
            wni = A_bar * yn[i]
            wn.append(wni)
        flat_wn = [item for sublist in wn for item in sublist]    
        print("flat_wn", flat_wn)

        print("Commitck...")  # 追加

        #trapdoor commitment    
        # パーティごとのコミットメントリストを初期化
        comn_per_party = [[] for _ in range(party_number)]
        #CGen
        ahat1_1 = generate_invertible_matrix(sigma, Rq)
        ahat1_j = Matrix(Rq, 1, trapl + 2*trapw - 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
        ahat2_j = Matrix(Rq, 1, trapl + 2*trapw - 2, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
        list1 = [Rq(0), Rq(1)]
        matrix_list1 = Matrix(Rq, [list1])
        matrix_up = ahat1_1.augment(ahat1_j)
        matrix_down = matrix_list1.augment(ahat2_j)
        Ahat = matrix_up.stack(matrix_down)
        #Commitck
        # 入力がk×1となるため、係数ごとにコミットメントを行う
        for p in range(0, party_number * k): # それぞれの係数に行うため、party_number * k回必要
            r = Matrix(Rq, trapl + 2*trapw, 1, lambda i, j: discrete_gaussian_sampler(sigma, Rq))
            rn.append(r) # rnにrを保存しておく
            fleft = Ahat * r
            listzero = [Rq(0)]
            listwn = [flat_wn[p]] # 順に係数を取り出す
            print('listwn', listwn)
            matrix_zero = Matrix(Rq, [listzero])
            matrix_wn = Matrix(Rq, 1, 1, [listwn])
            fright = matrix_zero.stack(matrix_wn)
            f = fleft + fright

            # p // kを使用して、現在の係数がどのパーティに属しているかを決定し、そのパーティのサブリストに追加
            comn_per_party[p // k].append(f)
            
        print("rn lens: ", len(rn))
        
        for i in range(party_number*k):
            print("rn dimensions: {0} x {1}".format(rn[i].nrows(), rn[i].ncols()))
            print("rn_type", type(rn[i]))

        # それぞれのパーティごとに計算されたコミットメントを表示
        for party_index, party_comn in enumerate(comn_per_party):
            print(f"Party {party_index} commitments: {party_comn}")
            
        # comn_per_partyの全体の大きさ（パーティの数）を出力
        print("Total number of parties:", len(comn_per_party))

        # 各パーティのコミットメントの数を出力
        for party_index, party_comn in enumerate(comn_per_party):
            print(f"Party {party_index} has {len(party_comn)} commitments.")

    # 2.Upon receiving comj for all j ∈ [n − 1] compute the signature share as follows.   
        if abort_flag:
            return "abort"
        else:
            # Party 0 と Party 1 のコミットメントを足し合わせる
            com_sum = sum_commitments(comn_per_party)

            # 足し合わせたコミットメントと大きさを表示
            print("Combined commitments for all parties:", com_sum)
            print("Len of com_sum :", len(com_sum))
            c = H0(com_sum, message, pk)
            print("challenge", c)
            print('ctype', type(c))
            print("skn", skn)
            csn = [[c * element for element in row] for row in skn]
            csn = [vector(Rq, [Rq(x) for x in row]) for row in csn]
            print("csn", csn)
            zn = [csn_elem + yn_elem for csn_elem, yn_elem in zip(csn, yn)]
            print("zn", zn)
            restart = False
            
#             rohs_rm = rohs_rm_cal(zn, s)
#             print('rohs_rm', rohs_rm)
#             rohcsn_s_rm = rohcsn_s_rm_cal(zn, csn, s)
#             print('rohcsn_s_rm', rohcsn_s_rm)
            
            result = rejection_sample(csn, zn)
            if result == "restart":
                    print("Restarting the protocol inside signature generation...") 
                    restart = True  
                    continue
            elif result:  
                csn_result, zn_result = result  
            else:
                # rejection_sample が None または偽の値を返した場合の処理
                print("rejection_sample から予期しない結果が返されました")
                break  # ループを抜けるか、他のエラーハンドリングを行う



    #3.Upon receiving restart from some party go to 1. Otherwise upon receiving (zj , rj ) for all j ∈ [n − 1] compute the combined signature as follows
        # a. For each j in [n-1], reconstruct wj and validate the signature share
        recon_wn = []
        print(len(zn_result))
        print(len(rn))
        print(len(tn))
        print('lencomn_per_party', len(comn_per_party))
        flat_comn_per_party = [item for sublist in comn_per_party for item in sublist]
        print('lenflatcomn_per_party', len(flat_comn_per_party))
        for zn_result, rn, tn, flat_comn_per_party in zip(zn_result, rn, tn, flat_comn_per_party):
            print(type(A_bar))
            print(type(zn_result))
            print(type(c))
            print(type(tn))        
            print(type(rn))
            print(type(Ahat))
            recon_wn_left = A_bar * zn_result
            print('recon_wn_left', recon_wn_left)
            recon_wn_right = c * tn
            recon_wn = recon_wn_left - recon_wn_right
            # recon_wnは多項式
            recon_wn_list = [recon_wn]
            print('recon_wn', recon_wn)
            # Openck のチェック
            for i in range(party_number):
                if Openck(Ahat, flat_comn_per_party, recon_wn[i], rn) == 0:
                    return "abort"

            # 追加の条件を確認
            if zn_result.norm() > B:
                return "abort"
            
            recon_wn.append(wn)

        # b. Compute z and r
        z = sum(zn_result)
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
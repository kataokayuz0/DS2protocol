import time
import matplotlib.pyplot as plt
import numpy as np
import math
import hashlib
import itertools
import csv
from sage.all import *
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler
from sage.modules.free_module_element import vector as sage_vector


# 実行時間を記録するリストを初期化
execution_times = []

for party_number in range(2, 101):
    # 各パーティ数に対する5回の実行時間を格納するリスト
    times_for_each_party = []
    
    for _ in range(5):  # 各パーティ数で5回の実行を行う
        start_time = time.time()
        # Parameters
        number = 2 ** 46
        next_prime_number = next_prime(number)
        while next_prime_number % 8 != 5:
            next_prime_number = next_prime(next_prime_number)
        q = next_prime_number
        # print(q)
        n = 256
        k, l = 14, 10
        sigma = 3  # Standard deviation for Gaussian sampler

        # Define the ring Rq
        R.<x> = PolynomialRing(ZZ)
        Zq = Integers(q)
        Rq = PolynomialRing(Zq, 'x').quotient(x^n + 1)


        #グローバル変数にする
        D = DiscreteGaussianDistributionIntegerSampler(sigma=sigma)
        def discrete_gaussian_sampler(ring):
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
            matrix = Matrix(Rq, k, l, lambda i, j: discrete_gaussian_sampler(Rq))
            matrices.append(matrix)
            # print(matrices)

        # Commitments for each party
        gn = []
        for i, matrix in enumerate(matrices):
            commitment = H1(matrix, i + 1)
            gn.append(commitment)

        # print("Commitments stored in gn:", gn)


        # 1. Upon receiving gj for all j ∈ [n − 1] send out An.
        An = matrices
        # print("Sending out An:", An)

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
            # print("Public random matrix A¯:\n", A_bar)


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
        # print(sn)

        tn = [A_bar * vector(ZZ, s) for s in sn]
        # print(tn)

        g_prime_n = []
        for i in range(party_number):
            g_prime_n_element = H2(tn[i], i)
            g_prime_n.append(g_prime_n_element)
        # print("Sending out g'n:", g_prime_n)

        # 2. Upon receiving g'j for all j ∈ [n − 1] send out tn.
        # print("Sending out tn:", tn)

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
            # print("Combined public key t:", t_combined)

        # Local output for Pn
        skn = sn
        pk = (A, t_combined)
        #print("Local output for Pn (skn, pk):", skn, pk)
        # print("skn", skn)
        # print("pk", pk)
            

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
        # print("Per-message commitment key ck:", ck)
        
        # Parameters
        eta = 5
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
        from concurrent.futures import ThreadPoolExecutor

        # 可逆であることを確認する関数を定義
        def is_invertible(m, Rq):
            try:
                _ = m.inverse()
                return True
            except:
                return False

        # 可逆な行列を生成する関数を定義
        def generate_invertible_matrix(Rq):
            while True:
                # ランダムな1x1行列を生成
                ahat1_1 = Matrix(Rq, 1, 1, lambda i, j: discrete_gaussian_sampler(Rq))
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
            return vector(ZZ, [(a + q // 2).lift() - q // 2 for a in z])

        def lift_ringeltvec_to_integervec(z):
            chain_result = list(itertools.chain(*[lift_ringelt_to_integervec(xi) for xi in z]))
            return vector(ZZ, chain_result)        

        def lift_vector_to_integervec(vec):
            return vector(ZZ, [lift_ringelt_to_integervec(v)[0] for v in vec])

        def lift_sampled_rn_to_integer(sampled_rn):
            return [lift_vector_to_integervec(vec) for vec in sampled_rn]

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
            
            rohs_zn = exp(-pi * (x_lifted.norm()) /  s^2)
            return rohs_zn / rohs_rm

        def Dcsn_s(v, x, s, rohcsn_s_rm):
            x_v_lifted = lift_ringeltvec_to_integervec(x-v)
            rohcsn_s_zn = exp(-pi * (x_v_lifted.norm()) /  s^2)
            return rohcsn_s_zn / rohcsn_s_rm

        #a. sample yn and compute wn
        def sampleyn():
            sample_yn = [vector(Rq, [discrete_gaussian_sampler(Rq) for _ in range(l+k)]) for _ in range(party_number)]
            return sample_yn

        def computewn(A_bar, sampled_yn):
            wn = []
            for i in range(party_number):
                    wni = A_bar * sampled_yn[i]
                    wn.append(wni)
            flat_wn = [item for sublist in wn for item in sublist]  
            return flat_wn


        #b. compute comn with rn

        def sample_from_S_r(size):
            # rの範囲内で整数をサンプリングする関数を定義
            return ZZ.random_element(-size, size+1)

        def samplern():
            sampled_rn = []
            for _ in range(party_number * k):
                # rの範囲内で整数をサンプリングし、それを行列の要素として使用
                r_matrix = Matrix(ZZ, trapl + 2*trapw, 1, lambda i, j: sample_from_S_r(eta))
                sampled_rn.append(r_matrix)
            return sampled_rn


        def CGen():
            ahat1_1 = generate_invertible_matrix(Rq)
            ahat1_j = Matrix(Rq, 1, trapl + 2*trapw - 1, lambda i, j: discrete_gaussian_sampler(Rq))
            ahat2_j = Matrix(Rq, 1, trapl + 2*trapw - 2, lambda i, j: discrete_gaussian_sampler(Rq))
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
                # print('listwn', listwn)
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

        # R上の多項式に係数をランダムに配置
        def H0(com, message, pk, N, kappa):
            R = PolynomialRing(ZZ, 'x')
            x = R.gen()

            # 入力からユニークなシード値を生成
            seed_str = str(com) + str(message) + str(pk)
            seed_val = int(hashlib.sha256(seed_str.encode()).hexdigest(), 16)

            # ランダム関数のシードを設定
            random.seed(seed_val)

            # kappa 個の位置をランダムに選択
            positions = random.sample(range(N), kappa)

            # 選択された位置に 1 または -1 をランダムに配置
            challenge = sum(random.choice([-1, 1]) * x^pos for pos in positions)

            # 係数が配置されていない位置には 0 を配置
            challenge += sum(0 * x^i for i in range(N) if i not in positions)
            return challenge

        #c. Computes a signature share
        def computezn(challenge, skn, yn):
            csn = [[challenge * element for element in row] for row in skn]
            csn = [vector(Rq, [Rq(x) for x in row]) for row in csn]
            computed_zn = [csn_elem + yn_elem for csn_elem, yn_elem in zip(csn, yn)]
            return computed_zn, csn

        #d. Run the rejection sampling
        c = 1

        def calculate_M(party_number, c):
            mn_list =[]
            for i in range(party_number):
                mn = math.exp(c / (party_number+1))
                mn_list.append(mn)
            return mn_list

        def rejection_sample(csn_list, zn_list, c):
            # print("Starting rejection_sampling...")  # 追加
            rejec_zn_result = []
            rohs_rm, rohcsn_s_rm = calculate_sums(csn_list, zn_list, s)
            mn_list = calculate_M(party_number, c)
            for csn, zn, mn in zip(csn_list, zn_list, mn_list):
                csn_vec = vector(Rq, csn)
                zn_vec = vector(Rq, zn)

                # 比率を計算
                ratio = Ds(zn_vec, s, rohs_rm) / (mn * Dcsn_s(csn_vec, zn_vec, s, rohcsn_s_rm))

                # 比率と1の小さい方を選ぶ
                acceptance_probability = min(1, ratio)
                random_probability = random.random()
                # print("acceptance_probability", acceptance_probability)
                # print("random_probability", random_probability)

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
                derived_challenge = H0(com, message, pk, N, kappa)
                computed_zn, csn = computezn(derived_challenge, skn, sampled_yn)
                result = rejection_sample(csn, computed_zn, c)
                if result == "restart":
                    continue
                else:
                    zn_result = result
                    break

            return com, Ahat, comn_per_party, matrix_zero, derived_challenge, sampled_rn, zn_result
                    
        com, Ahat, comn_per_party, matrix_zero, derived_challenge, sampled_rn, zn_result = sig1_sig2() 


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
                # print(type(recon_wn_left), type(recon_wn_right))
                reconted_wj.append(recon_wn_left - recon_wn_right)
            return reconted_wj

        def validate_zn(zn_result):
            for i in range(0, party_number):
        #         print('zn_result', zn_result)
        #         print('len_zn_result', len(zn_result))
        #         print('type_zn_result', type(zn_result))
                zn_result_lifted = lift_ringeltvec_to_integervec(zn_result[i])
                zn_result_lifted_norm = zn_result_lifted.norm()
        #         print('zn_result_lifted_norm', zn_result_lifted_norm)
                if zn_result_lifted_norm > B:
                    return "abort"

        def validate_openck(sampled_rn, reconted_wj, matrix_zero, comn_per_party):
            flat_comn_per_party = [item for sublist in comn_per_party for item in sublist]
            flat_reconted_wj = [item for sublist in reconted_wj for item in sublist]
            for i in range(party_number*k):
                openck_fleft = Ahat * sampled_rn[i]
                openck_matrix_wn = Matrix(Rq, 1, 1, flat_reconted_wj[i])
                openck_zero_x = matrix_zero.stack(openck_matrix_wn)
                openck_result = openck_fleft + openck_zero_x
                sampled_rn_lifted = sampled_rn[i]
                norms = [vec.norm() for vec in sampled_rn_lifted]
                # print('flat_comn_per_party[i]', flat_comn_per_party[i])
                # print('openck_result', openck_result)
                if not(all(n <= B for n in norms) and flat_comn_per_party[i] == openck_result):
                    return "abort"
                else:
                    return 1
        
        #b. compute z  and r
        def compute_signature(zn_result, sampled_rn, k):
            sign_zn = sum(zn_result)
            # kごとにリストを分割し、分割されたリストをそれぞれ合計する
            sign_rn_list = [sum(sampled_rn[i::k]) for i in range(k)]
            return (sign_zn, sign_rn_list)

        reconted_wj = recon_wj(A_bar, zn_result, derived_challenge, tn)
        # print('reconted_wj', reconted_wj)
        # print('len_reconted_wj', len(reconted_wj))
        # print('type_reconted_wj', type(reconted_wj))

        if validate_zn(zn_result) == "abort":
            print("protocol aborted.")
        elif validate_openck(sampled_rn, reconted_wj, matrix_zero, comn_per_party) == "abort":
            print("protocol aborted.")
        else:
            sign_zn, sign_rn_list = compute_signature(zn_result, sampled_rn, k)
            # print('sign_zn', sign_zn)
            # print('sign_rn_list', sign_rn_list)
            # print(type(sign_zn))
            # print(type(sign_rn_list))
            
        
        def ready_verification(com, sign_zn, message, pk):
            ver_ck = H3(message, pk, ck_limit)
            ver_c = H0(com, message, pk, N, kappa)
            ver_w = (A_bar * sign_zn) - (ver_c * t_combined)
            return ver_w

        def eachparty_openck(sign_rn_list, ver_w, matrix_zero, com):
            for j in range(k):
                sign_rn_lifted = sign_rn_list[j]
                sign_rn_norms = [vec.norm() for vec in sign_rn_lifted]
                each_openck_fleft = Ahat * sign_rn_list[j]
                each_openck_matrix_wn = Matrix(Rq, 1, 1, ver_w[j])
                each_openck_zero_x = matrix_zero.stack(each_openck_matrix_wn)
                each_openck_result = each_openck_fleft + each_openck_zero_x
                # print('con[j]', com[j])
                # print('each_openck_result', each_openck_result)
                if all(n <= B for n in sign_rn_norms) and com[j] == each_openck_result:
                    return 1
                else:
                    print("eachparty_openck is aborted")
                    return "abort"

        def eachparty_verification(sign_zn, com, sign_rn_list, ver_w):
            sign_zn_lifted = lift_ringeltvec_to_integervec(sign_zn)
            sign_zn_lifted_norm = sign_zn_lifted.norm()
            verification_failed = False
            for i in range(party_number):
                cal_n = i + 1 
                Bn = sqrt(cal_n) * B
                if (sign_zn_lifted_norm > Bn) or (eachparty_openck(sign_rn_list, ver_w, matrix_zero, com) != 1):
                    print("verification is invalid")
                    verification_failed = True
                    break
            if not verification_failed:
                print("verification is valid")


        ver_w = ready_verification(com, sign_zn, message, pk)
        eachparty_verification(sign_zn, com, sign_rn_list, ver_w)   
        # リストに実行時間を追加
        end_time = time.time()
        times_for_each_party.append(end_time - start_time)  # 実行時間をリストに追加
        
    # 5回の実行時間の平均を計算し、リストに追加
    average_time = sum(times_for_each_party) / len(times_for_each_party)
    execution_times.append(average_time)
    
# 実行時間をCSVファイルに保存
with open('execution_times.csv', 'w', newline='') as file:
    writer = csv.writer(file)
    writer.writerow(['party_number', 'average_execution_time'])
    for pn, et in zip(range(2, 101), execution_times):
        writer.writerow([pn, et])

# 実行時間の平均をプロット
plt.plot(range(2, 101), execution_times)
plt.xlabel('party_number')
plt.ylabel('average_execution_time (sec)')
plt.title('Average Execution Times for DS2 Protocol')
plt.show()
#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# Unit tests for RM_code (binary Reed-Muller codes).
# ================================================================

require 'RM_code.rb'
require 'test/unit'

class RM_codeUnitTest < Test::Unit::TestCase

	# ------------------------------------------------------------
	def int_to_bv(len, x)
		bv = Bit_vector.new(len)
		bv.bits = x
		bv
	end

	def all_error_patterns(n, max_weight)
		patterns = []
		for w in 1..max_weight
			(0...n).to_a.combination(w) do |posns|
				e = 0
				posns.each { |p| e |= 1 << p }
				patterns.push(e)
			end
		end
		patterns
	end

	# ------------------------------------------------------------
	def test_parameters
		rm = RM_code.new(0, 4)
		assert_equal(16, rm.n)
		assert_equal(1, rm.k)
		assert_equal(16, rm.dmin)
		assert_equal(7, rm.t)

		rm = RM_code.new(1, 3)
		assert_equal(8, rm.n)
		assert_equal(4, rm.k)
		assert_equal(4, rm.dmin)
		assert_equal(1, rm.t)

		rm = RM_code.new(2, 4)
		assert_equal(16, rm.n)
		assert_equal(11, rm.k)
		assert_equal(4, rm.dmin)
		assert_equal(1, rm.t)

		rm = RM_code.new(2, 5)
		assert_equal(32, rm.n)
		assert_equal(16, rm.k)
		assert_equal(8, rm.dmin)
		assert_equal(3, rm.t)

		rm = RM_code.new(3, 3)
		assert_equal(8, rm.k)
		assert_equal(1, rm.dmin)

		assert_raise(RuntimeError) { RM_code.new(4, 3) }
		assert_raise(RuntimeError) { RM_code.new(-1, 3) }
	end

	# ------------------------------------------------------------
	# Variable and evaluation-point orderings are public, so that
	# codewords can be checked independently of this implementation.
	def test_public_orderings
		rm = RM_code.new(2, 3)
		assert_equal(["x0", "x1", "x2"], rm.variables)
		assert_equal((0..7).to_a, rm.eval_points)
		# Point j: bit i of j is the value of x_i.
		assert_equal([0, 0, 0], rm.eval_point_bits(0))
		assert_equal([1, 1, 0], rm.eval_point_bits(3))
		assert_equal([0, 1, 1], rm.eval_point_bits(6))
		# Monomials: increasing degree, lexicographic within a degree.
		assert_equal(
			[[], [0], [1], [2], [0, 1], [0, 2], [1, 2]],
			rm.monomials)
		assert_equal(
			["1", "x0", "x1", "x2", "x0*x1", "x0*x2", "x1*x2"],
			rm.monomial_strings)
	end

	# ------------------------------------------------------------
	def test_generator_rm_1_3
		Bit_matrix.set_binary_output
		rm = RM_code.new(1, 3)
		# Rows: 1, x0, x1, x2 evaluated at points j = 0..7
		# (printed with position 7 leftmost).
		assert_equal(
			"11111111\n" \
			"10101010\n" \
			"11001100\n" \
			"11110000\n",
			rm.generator.to_s)
		assert_equal(rm.k, rm.generator.rank)
	end

	def test_generator_full_rank
		[[0, 3], [1, 4], [2, 4], [2, 5], [3, 5]].each do |r, m|
			rm = RM_code.new(r, m)
			assert_equal(rm.k, rm.generator.rank, "rank for RM(#{r},#{m})")
		end
	end

	# ------------------------------------------------------------
	# Minimum distance = minimum nonzero codeword weight (linear code),
	# checked by enumerating all info words of small codes.
	def test_minimum_distance_by_enumeration
		[[1, 3], [1, 4], [2, 4], [0, 4]].each do |r, m|
			rm = RM_code.new(r, m)
			min_weight = rm.n
			for info_int in 1...((1 << rm.k))
				cw = rm.encode(int_to_bv(rm.k, info_int))
				w = RM_code.hamming_int(cw.bits)
				min_weight = w if w < min_weight
			end
			assert_equal(rm.dmin, min_weight, "dmin for RM(#{r},#{m})")
		end
	end

	# ------------------------------------------------------------
	# Enumerate all info words of a small code; clean channel.
	def test_encode_decode_all_info_words_no_errors
		rm = RM_code.new(2, 4) # k = 11: all 2048 info words
		for info_int in 0...(1 << rm.k)
			info = int_to_bv(rm.k, info_int)
			codeword = rm.encode(info)
			result = rm.decode(codeword)
			assert_equal(0, result.distance)
			assert(result.guaranteed)
			assert_equal(0, result.ties)
			assert_equal(info_int, result.info.bits)
		end
	end

	# ------------------------------------------------------------
	# Enumerate all info words of a small code, then inject every
	# error pattern within the guaranteed correction radius.
	def test_corrects_all_errors_within_radius
		rm = RM_code.new(1, 4) # n=16, k=5, dmin=8, t=3
		patterns = all_error_patterns(rm.n, rm.t)
		assert_equal(16 + 120 + 560, patterns.length)
		for info_int in 0...(1 << rm.k)
			codeword = rm.encode(int_to_bv(rm.k, info_int))
			patterns.each do |e|
				received = int_to_bv(rm.n, codeword.bits ^ e)
				result = rm.decode(received)
				assert(result.guaranteed,
					"not guaranteed: info=#{info_int} e=#{e}")
				assert_equal(info_int, result.info.bits,
					"wrong decode: info=#{info_int} e=#{e}")
				assert_equal(RM_code.hamming_int(e), result.distance)
			end
		end
	end

	# ------------------------------------------------------------
	# Beyond the correction radius the decoder must not claim a
	# guarantee; it still returns a candidate and its distance.
	def test_beyond_radius_is_honest
		rm = RM_code.new(1, 4) # t = 3
		patterns = all_error_patterns(rm.n, 6) - all_error_patterns(rm.n, rm.t)
		not_guaranteed_count = 0
		for info_int in [0, 1, 5, 17, 31]
			codeword = rm.encode(int_to_bv(rm.k, info_int))
			patterns.each do |e|
				received = int_to_bv(rm.n, codeword.bits ^ e)
				result = rm.decode(received)
				# Consistency: a guarantee is claimed only within radius.
				assert_equal(2 * result.distance < rm.dmin,
					result.guaranteed)
				if result.guaranteed
					# A claimed guarantee must be truthful: the
					# candidate is then the unique closest codeword.
					assert(result.distance <= rm.t)
				else
					not_guaranteed_count += 1
				end
			end
		end
		# Most weight-(t+1) or heavier injections are honestly flagged.
		assert(not_guaranteed_count > 0)
	end

	def test_beyond_radius_reports_candidate_and_distance
		rm = RM_code.new(1, 3) # t = 1
		codeword = rm.encode(int_to_bv(rm.k, 0))
		# Weight 2 > t; no codeword lies within distance 1 of this
		# received word (nonzero codewords have weight 4 or 8), so
		# no guarantee may be claimed.
		received = int_to_bv(rm.n, codeword.bits ^ 0b00000011)
		result = rm.decode(received)
		assert_equal(2 * result.distance < rm.dmin, result.guaranteed)
		assert(!result.guaranteed)
		assert_not_nil(result.info)
		assert_not_nil(result.codeword)
		assert(result.distance >= 0)
	end

	# ------------------------------------------------------------
	# RM(0, m) is the repetition code.
	def test_repetition_code
		rm = RM_code.new(0, 3) # n=8, dmin=8, t=3
		assert_equal("11111111", rm.encode(int_to_bv(1, 1)).to_s)
		assert_equal("00000000", rm.encode(int_to_bv(1, 0)).to_s)
		received = int_to_bv(8, 0b00010111) # 4 ones, 4 zeros: tied vote
		result = rm.decode(received)
		assert(!result.guaranteed)
		assert(result.ties > 0)
		received = int_to_bv(8, 0b00101111) # 5 ones
		result = rm.decode(received)
		assert(result.guaranteed)
		assert_equal(1, result.info.bits)
	end

	# ------------------------------------------------------------
	# RM(3,7) has k = 64 info bits: enumerating all 2^64 info words
	# (or all 2^64 codewords for nearest-neighbor decoding) is
	# infeasible.  Majority-logic decoding handles it directly.
	def test_large_code_decodes_without_enumeration
		rm = RM_code.new(3, 7) # n=128, k=64, dmin=16, t=7
		assert_equal(64, rm.k)
		srand(804)
		for trial in 1..8
			info_int = (1..4).map { rand(1 << 30) }.inject { |a, b| (a << 30) | b }
			info_int &= (1 << rm.k) - 1
			codeword = rm.encode(int_to_bv(rm.k, info_int))
			e = 0
			(0...rm.n).to_a.sample(rm.t).each { |p| e |= 1 << p }
			received = int_to_bv(rm.n, codeword.bits ^ e)
			result = rm.decode(received)
			assert(result.guaranteed, "trial #{trial} not guaranteed")
			assert_equal(info_int, result.info.bits, "trial #{trial} wrong")
		end
	end

end

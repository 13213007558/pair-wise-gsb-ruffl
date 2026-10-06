#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# Tests for S_box: LAT/DDT/ANF/nonlinearity, using the identity
# map and non-bijective maps, with Parseval and DDT row-sum checks.
# Fast transforms are cross-checked against brute-force definitions.
# ================================================================

require 'S_box.rb'
require 'test/unit'

class S_boxUnitTest < Test::Unit::TestCase

	# ----------------------------------------------------------------
	# Brute-force LAT straight from the definition (no fast transform).
	def brute_lat(sbox)
		n = sbox.num_input_bits
		m = sbox.num_output_bits
		lat = Array.new(1 << n) { Array.new(1 << m, 0) }
		(0 ... (1 << n)).each do |a|
			(0 ... (1 << m)).each do |b|
				sum = 0
				(0 ... (1 << n)).each do |x|
					p = S_box.inner_product(a, x) ^ S_box.inner_product(b, sbox.table[x])
					sum += (p == 0) ? 1 : -1
				end
				lat[a][b] = sum
			end
		end
		lat
	end

	# Brute-force ANF: c[u] = XOR of f(x) over all x whose set bits are
	# a subset of the bits of u (definition of the Moebius transform).
	def brute_anf(truth)
		size = truth.length
		(0 ... size).map do |u|
			c = 0
			(0 ... size).each do |x|
				c ^= truth[x] if (x & ~u) == 0
			end
			c
		end
	end

	def brute_nonlinearity(sbox)
		n = sbox.num_input_bits
		lat = brute_lat(sbox)
		best = 0
		(1 ... (1 << sbox.num_output_bits)).each do |b|
			(0 ... (1 << n)).each do |a|
				best = lat[a][b].abs if lat[a][b].abs > best
			end
		end
		(1 << (n - 1)) - best / 2
	end

	def assert_parseval(sbox)
		n = sbox.num_input_bits
		(0 ... (1 << sbox.num_output_bits)).each do |b|
			sum_of_squares = (0 ... (1 << n)).inject(0) { |s, a| s + sbox.lat[a][b]**2 }
			assert_equal(1 << (2 * n), sum_of_squares, "Parseval failed for output mask #{b}")
		end
	end

	def assert_ddt_row_sums(sbox)
		sbox.ddt.each_with_index do |row, a|
			assert_equal(1 << sbox.num_input_bits, row.inject(:+), "DDT row #{a} sum")
		end
	end

	# ----------------------------------------------------------------
	def test_constructor_validation
		assert_raise(RuntimeError) { S_box.new([0, 1, 2]) }
		assert_raise(RuntimeError) { S_box.new([0, 1, 2, 8], 3) }
		assert_raise(RuntimeError) { S_box.new([0, -1]) }
		s = S_box.new([0, 1, 2, 3], 3)
		assert_equal(2, s.num_input_bits)
		assert_equal(3, s.num_output_bits)
		s = S_box.new([0, 1, 2, 3])
		assert_equal(2, s.num_output_bits)
	end

	# ----------------------------------------------------------------
	def test_fast_transforms
		# FWT of a point mass is constant; FWT is self-inverse up to 2**n.
		assert_equal([1, 1, 1, 1], S_box.fast_walsh_transform([1, 0, 0, 0]))
		f = [3, -1, 0, 2, 5, 7, -4, 1]
		g = S_box.fast_walsh_transform(S_box.fast_walsh_transform(f.dup))
		assert_equal(f.map { |e| e * 8 }, g)
		# Moebius transform is an involution over GF(2).
		t = [1, 0, 1, 1, 0, 1, 0, 0]
		assert_equal(t, S_box.mobius_transform(S_box.mobius_transform(t.dup)))
	end

	# ----------------------------------------------------------------
	def test_identity_map
		sbox = S_box.new([0, 1, 2, 3, 4, 5, 6, 7])
		assert_equal(3, sbox.num_input_bits)
		assert_equal(3, sbox.num_output_bits)

		# Identity: LAT[a][b] = 8 iff a == b, else 0.
		(0 ... 8).each do |a|
			(0 ... 8).each do |b|
				assert_equal(a == b ? 8 : 0, sbox.lat[a][b], "LAT[#{a}][#{b}]")
			end
		end
		assert_equal(sbox.lat, brute_lat(sbox))
		assert_parseval(sbox)

		# Identity: S(x) ^ S(x^a) = a, so DDT[a][a] = 8 and DDT[0][0] = 8.
		(0 ... 8).each do |a|
			(0 ... 8).each do |b|
				assert_equal(a == b ? 8 : 0, sbox.ddt[a][b], "DDT[#{a}][#{b}]")
			end
		end
		assert_ddt_row_sums(sbox)

		# Identity components are single variables: degree 1, zero nonlinearity.
		assert_equal([0, 1, 0, 0, 0, 0, 0, 0], sbox.anf(0))
		assert_equal([0, 0, 1, 0, 0, 0, 0, 0], sbox.anf(1))
		assert_equal([0, 0, 0, 0, 1, 0, 0, 0], sbox.anf(2))
		(0 ... 3).each { |j| assert_equal(1, sbox.algebraic_degree(j)) }
		assert_equal(1, sbox.algebraic_degree_all)
		assert_equal(8, sbox.max_lat_entry)
		assert_equal(0, sbox.nonlinearity)
		assert_equal(0, brute_nonlinearity(sbox))
	end

	# ----------------------------------------------------------------
	def test_non_bijective_map
		# 3 -> 2 bits, surjective but not injective (each value hit twice).
		sbox = S_box.new([3, 0, 2, 1, 1, 2, 0, 3])
		assert_equal(3, sbox.num_input_bits)
		assert_equal(2, sbox.num_output_bits)
		assert_equal([0, 1, 2, 3], sbox.table.sort.uniq)

		assert_equal(brute_lat(sbox), sbox.lat)
		assert_parseval(sbox)
		assert_ddt_row_sums(sbox)
		assert_equal(8, sbox.ddt[0][0])

		(0 ... 2).each do |j|
			truth = sbox.table.map { |y| (y >> j) & 1 }
			assert_equal(brute_anf(truth), sbox.anf(j), "ANF of y#{j}")
		end
		assert_equal(brute_nonlinearity(sbox), sbox.nonlinearity)
	end

	# ----------------------------------------------------------------
	def test_non_surjective_map
		# 3 -> 2 bits, image misses output value 3.
		sbox = S_box.new([0, 0, 1, 1, 2, 2, 1, 0], 2)
		assert_equal(brute_lat(sbox), sbox.lat)
		assert_parseval(sbox)
		assert_ddt_row_sums(sbox)
		(0 ... 2).each do |j|
			truth = sbox.table.map { |y| (y >> j) & 1 }
			assert_equal(brute_anf(truth), sbox.anf(j), "ANF of y#{j}")
		end
		assert_equal(brute_nonlinearity(sbox), sbox.nonlinearity)
	end

	# ----------------------------------------------------------------
	def test_differing_bit_widths
		# 2 -> 3 bits.
		sbox = S_box.new([0, 5, 6, 3])
		assert_equal(2, sbox.num_input_bits)
		assert_equal(3, sbox.num_output_bits)
		assert_equal(brute_lat(sbox), sbox.lat)
		assert_parseval(sbox)
		assert_ddt_row_sums(sbox)
		(0 ... 3).each do |j|
			truth = sbox.table.map { |y| (y >> j) & 1 }
			assert_equal(brute_anf(truth), sbox.anf(j), "ANF of y#{j}")
		end
		assert_equal(brute_nonlinearity(sbox), sbox.nonlinearity)
	end

	# ----------------------------------------------------------------
	def test_constant_map
		# Degenerate non-bijective map: all components are constants.
		sbox = S_box.new([2, 2, 2, 2], 2)
		assert_equal(-1, sbox.algebraic_degree(0)) # zero function
		assert_equal(0, sbox.algebraic_degree(1))  # constant 1
		assert_equal(0, sbox.nonlinearity)
		assert_parseval(sbox)
		assert_ddt_row_sums(sbox)
	end

	# ----------------------------------------------------------------
	def test_report
		sbox = S_box.new([3, 0, 2, 1, 1, 2, 0, 3])
		r = sbox.report
		assert(r.include?("3 input bits, 2 output bits"))
		assert(r.include?("Linear approximation table"))
		assert(r.include?("Difference distribution table"))
		assert(r.include?("Algebraic normal forms"))
		assert(r.include?("Nonlinearity"))
		assert(r.include?("bit 0 = LSB"))
	end

	# ----------------------------------------------------------------
	def test_anf_to_s
		assert_equal("0", S_box.anf_to_s([0, 0, 0, 0], 2))
		assert_equal("1", S_box.anf_to_s([1, 0, 0, 0], 2))
		assert_equal("x0", S_box.anf_to_s([0, 1, 0, 0], 2))
		assert_equal("1 ^ x0 ^ x0*x1", S_box.anf_to_s([1, 1, 0, 1], 2))
	end

end

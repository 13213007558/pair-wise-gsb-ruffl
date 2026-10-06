#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# John Kerl
# kerl.john.r@gmail.com
# Copyright (c) 2011
# ================================================================

require 'Sbox_analysis.rb'
require 'test/unit'

class Sbox_analysisUnitTest < Test::Unit::TestCase

	# 3-bit identity permutation.
	def setup
		@id3 = Sbox.new([0, 1, 2, 3, 4, 5, 6, 7])
		# 3 -> 2 bits, not a bijection:  each output value hit twice.
		@fold = Sbox.new([0, 1, 2, 3, 3, 2, 1, 0])
		# 2 -> 1 bit Boolean functions.
		@xor2 = Sbox.new([0, 1, 1, 0])
		@and2 = Sbox.new([0, 0, 0, 1])
		# PRESENT 4-bit S-box (a bijection with known metrics).
		@present = Sbox.new([0xc, 5, 6, 0xb, 9, 0, 0xa, 0xd,
			3, 0xe, 0xf, 8, 4, 7, 1, 2])
	end

	def test_constructor
		assert_equal(3, @id3.num_in_bits)
		assert_equal(3, @id3.num_out_bits)
		assert_equal(3, @fold.num_in_bits)
		assert_equal(2, @fold.num_out_bits)
		assert_raise(RuntimeError) { Sbox.new([0, 1, 2]) }
		assert_raise(RuntimeError) { Sbox.new([0, 4], 1) }
	end

	def test_fwht_inverts_itself_up_to_scale
		f = [3, -1, 0, 2, 5, 7, -4, 1]
		g = Sbox.fwht(f.dup)
		h = Sbox.fwht(g)
		assert_equal(f.map { |v| v * 8 }, h)
	end

	def test_mobius_inverts_itself
		f = [1, 0, 1, 1, 0, 1, 0, 0]
		assert_equal(f, Sbox.mobius(Sbox.mobius(f.dup)))
	end

	# Identity map:  LAT[a][b] = 2**n iff a == b, else 0.
	def test_lat_identity
		lat = @id3.lat
		(0...8).each do |a|
			(0...8).each do |b|
				assert_equal(a == b ? 8 : 0, lat[a][b], "LAT[#{a}][#{b}]")
			end
		end
	end

	# Identity map:  S(x) ^ S(x ^ dx) = dx for all x.
	def test_ddt_identity
		ddt = @id3.ddt
		(0...8).each do |dx|
			(0...8).each do |dy|
				assert_equal(dx == dy ? 8 : 0, ddt[dx][dy], "DDT[#{dx}][#{dy}]")
			end
		end
	end

	def test_identity_metrics
		assert_equal(0, @id3.nonlinearity)
		assert_equal(1, @id3.algebraic_degree)
		assert_equal(8, @id3.differential_uniformity)
		assert_equal("x0", @id3.anf_to_s(0))
		assert_equal("x1", @id3.anf_to_s(1))
		assert_equal("x2", @id3.anf_to_s(2))
	end

	# Parseval and DDT row sums on the identity and on a non-bijective map.
	def test_parseval_and_row_sums
		[@id3, @fold, @xor2, @and2, @present].each do |s|
			assert(s.parseval_ok?)
			assert(s.ddt_row_sums_ok?)
			s.ddt.each { |row| assert_equal(s.num_in, row.inject(:+)) }
		end
	end

	# Non-bijective 3 -> 2 map:  LAT[0][0] = 8;  zero column of the DDT
	# beyond dx = 0 since outputs collide;  metrics stay consistent.
	def test_non_bijective
		assert_equal(8, @fold.lat[0][0])
		assert_equal(8, @fold.ddt[0][0])
		# dx = 4 flips the top input bit:  S(x ^ 4) = 3 - S(x), so the
		# output difference is constantly 3.
		assert_equal(8, @fold.ddt[4][3])
		assert_equal(0, @fold.nonlinearity)
		assert_equal(1, @fold.algebraic_degree)
	end

	def test_boolean_functions
		assert_equal("x0 + x1", @xor2.anf_to_s(0))
		assert_equal(1, @xor2.algebraic_degree)
		assert_equal(0, @xor2.nonlinearity)
		assert_equal("x0*x1", @and2.anf_to_s(0))
		assert_equal(2, @and2.algebraic_degree)
		assert_equal(1, @and2.nonlinearity)
	end

	# Known values for the PRESENT S-box.
	def test_present
		assert_equal(4, @present.nonlinearity)
		assert_equal(3, @present.algebraic_degree)
		assert_equal(4, @present.differential_uniformity)
		assert_equal(16, @present.lat[0][0])
		assert_equal(16, @present.ddt[0][0])
	end

	# Cross-check Walsh spectrum against its definition, brute force.
	def test_walsh_against_definition
		(0...4).each do |b|
			w = @fold.walsh_spectrum(b)
			(0...8).each do |a|
				expect = (0...8).inject(0) do |s, x|
					s + (Sbox.dot(a, x) ^ Sbox.dot(b, @fold.table[x]) == 0 ? 1 : -1)
				end
				assert_equal(expect, w[a], "W_#{b}(#{a})")
			end
		end
	end

	# Cross-check ANF against truth-table evaluation, brute force.
	def test_anf_against_truth_table
		(0...2).each do |bit|
			coeffs = @fold.anf(bit)
			(0...8).each do |x|
				val = 0
				(0...8).each do |m|
					val ^= coeffs[m] if (x & m) == m
				end
				assert_equal((@fold.table[x] >> bit) & 1, val, "bit #{bit} at #{x}")
			end
		end
	end

	def test_report
		r = Sbox.report_all([["id3", @id3], ["fold", @fold]])
		assert_match(/S-box id3:  3 input bits, 3 output bits/, r)
		assert_match(/S-box fold:  3 input bits, 2 output bits/, r)
		assert_match(/LAT/, r)
		assert_match(/DDT/, r)
		assert_match(/nonlinearity: 0/, r)
		assert_match(/DDT row sums == 8: true/, r)
		assert_match(/Parseval sum_a W_b\(a\)\^2 == 64: true/, r)
	end

end

#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
#
# John Kerl
# kerl.john.r@gmail.com
# Copyright (c) 2011
# ================================================================

require 'test/unit'

class Fec_unit_test < Test::Unit::TestCase

	# E: y^2+xy = x^3+x^2+1 over GF(4), 8 points including O.
	def test_feclist
		o = `feclist`; assert_not_equal($?, 0)
		o = `feclist 1 0 7`; assert_not_equal($?, 0) # singular
		o = `feclist 1 1 7`; assert_equal($?, 0)
		lines = o.split("\n")
		assert_equal("(0, 1)", lines[1])
		assert_equal("O", lines[-2])
		assert_equal("# 8 points (including O)", lines[-1])
	end

	def test_fecmul_ops
		o = `fecmul`; assert_not_equal($?, 0)
		o = `fecmul 1 1 7 dbl 1 3`; assert_equal($?, 0)
		assert_equal("(0, 1)\n", o)
		o = `fecmul 1 1 7 add 1 2 1 3`; assert_equal($?, 0)
		assert_equal("O\n", o)
		o = `fecmul 1 1 7 neg 1 2`; assert_equal($?, 0)
		assert_equal("(1, 3)\n", o)
		o = `fecmul 1 1 7 mul 3 1 3`; assert_equal($?, 0)
		assert_equal("(1, 2)\n", o)
	end

	def test_fecmul_compress
		o = `fecmul 1 1 7 comp 0 1`; assert_equal($?, 0)
		assert_equal("00:1\n", o)
		o = `fecmul 1 1 7 comp 1 2`; assert_equal($?, 0)
		assert_equal("1:0\n", o)
		o = `fecmul 1 1 7 dec 00:1`; assert_equal($?, 0)
		assert_equal("(0, 1)\n", o)
		o = `fecmul 1 1 7 dec 1:0`; assert_equal($?, 0)
		assert_equal("(1, 2)\n", o)
	end

	def test_fecmul_decompress_no_solution
		# GF(8), E: y^2+xy = x^3+1: x = 2 has no points.
		o = `fecmul 0 1 b dec 2:0`; assert_not_equal($?, 0)
		o = `fecmul 0 1 b dec 1:0`; assert_equal($?, 0)
		assert_equal("(1, 0)\n", o)
		o = `fecmul 1 1 7 dec nonsense`; assert_not_equal($?, 0)
	end

end

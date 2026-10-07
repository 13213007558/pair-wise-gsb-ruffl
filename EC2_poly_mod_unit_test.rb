#!/usr/bin/ruby -Wall

# ================================================================
# Please see LICENSE.txt in the same directory as this file.
# John Kerl
# kerl.john.r@gmail.com
# Copyright (c) 2011
# ================================================================

require 'EC2_poly_mod.rb'
require 'test/unit'

class EC2_poly_mod_unit_test < Test::Unit::TestCase

	# GF(4), f(t) = t^2 + t + 1 = 0x7.
	# E: y^2 + xy = x^3 + x^2 + 1 (a=1, b=1) is a curve of 8 points.
	F4 = 0x7
	# GF(8), f(t) = t^3 + t + 1 = 0xb.
	F8 = 0xb

	def test_construction_rejects_bad_inputs
		assert_raise(RuntimeError) {EC2_poly_mod_curve.new(1, 0, F4)} # b = 0, singular
		assert_raise(RuntimeError) {EC2_poly_mod_curve.new(1, 1, 0x1)} # degree < 1
		assert_raise(RuntimeError) {EC2_poly_mod_curve.new(1, 1, 0x1c)} # reducible mod

		e = EC2_poly_mod_curve.new(1, 1, F4)
		assert_raise(RuntimeError) {e.point(0, 0)} # not on the curve
		assert_raise(RuntimeError) {e.point(1, 0)} # not on the curve
	end

	def test_membership
		e = EC2_poly_mod_curve.new(1, 1, F4)
		assert_equal(true,  e.contains?(0, 1))
		assert_equal(true,  e.contains?(1, 2))
		assert_equal(true,  e.contains?(1, 3))
		assert_equal(true,  e.contains?(2, 1))
		assert_equal(true,  e.contains?(2, 3))
		assert_equal(true,  e.contains?(3, 1))
		assert_equal(true,  e.contains?(3, 2))
		assert_equal(false, e.contains?(0, 0))
		assert_equal(false, e.contains?(1, 0))
	end

	def test_membership_a0_curve
		# E: y^2 + xy = x^3 + 1 over GF(4).
		e = EC2_poly_mod_curve.new(0, 1, F4)
		assert_equal(true,  e.contains?(1, 0))
		assert_equal(true,  e.contains?(1, 1))
		assert_equal(true,  e.contains?(2, 0))
		assert_equal(true,  e.contains?(2, 2))
		assert_equal(true,  e.contains?(3, 3))
		assert_equal(true,  e.contains?(3, 0))
		assert_equal(false, e.contains?(2, 1))
	end

	def test_infinity_identity
		e = EC2_poly_mod_curve.new(1, 1, F4)
		o = e.infinity
		p = e.point(1, 2)
		assert_equal(true, o.infinity?)
		assert_equal(false, p.infinity?)
		assert_equal(o, o + o)
		assert_equal(p, o + p)
		assert_equal(p, p + o)
		assert_equal(o, p + (-p))
		assert_equal(o, e.add(p, e.negate(p)))
	end

	def test_enumeration_gf4
		e = EC2_poly_mod_curve.new(1, 1, F4)
		want = [[0,1],[1,2],[1,3],[2,1],[2,3],[3,1],[3,2]]
		got = e.points.collect {|p| [p.x.residue.bits, p.y.residue.bits]}.sort
		assert_equal(want, got)
	end

	# Exhaustive check over every small-field curve: closure,
	# commutativity, identity, inverses, doubling-vs-addition,
	# and Lagrange nP = O for every enumerated point.
	def test_group_law_all_small_curves
		[[F4, 0x7], [F8, 0xb]].each do |label, f|
			F2_poly_mod.elements_for_modulus(f).each do |a|
				F2_poly_mod.units_for_modulus(f).each do |b|
					e = EC2_poly_mod_curve.new(a, b, f)
					set = e.points + [e.infinity]
					n = set.length
					set.each do |p|
						assert_equal(e.infinity, n * p, "nP != O for #{e.inspect} #{p}")
						assert_equal(e.double(p), p + p)
						set.each do |q|
							s = p + q
							assert(set.include?(s), "sum off curve for #{e.inspect}: #{p}+#{q}=#{s}")
							assert_equal(s, q + p) # abelian
							assert_equal(p, s + (-q)) # (p+q)-q = p
						end
					end
				end
			end
		end
	end

	def test_x0_is_unique_order2_point
		e = EC2_poly_mod_curve.new(1, 1, F4)
		t = e.point(0, 1)
		assert_equal(e.infinity, e.double(t))
		assert_equal(e.infinity, t + t)
		assert_equal(t, -t) # x = 0 => x + y = y

		# roots_for_x(0) is not used; y_for_x0 gives the unique
		# square root of b.
		assert_equal(F2_poly_mod.new(1, F4), e.y_for_x0)
		assert_raise(RuntimeError) {e.roots_for_x(0)} # division by x^2
	end

	def test_doubling_formula
		# GF(8), E: y^2+xy = x^3 + 1, P = (1,0).
		e = EC2_poly_mod_curve.new(0, 1, F8)
		p = e.point(1, 0)
		# lambda = x + y/x = 1, x3 = 1+1 = 0, y3 = x^2 = 1.
		assert_equal(e.point(0, 1), e.double(p))
		assert_equal(e.infinity, e.double(e.point(0, 1)))
	end

	def test_scalar_mult
		e = EC2_poly_mod_curve.new(0, 1, F4)
		g = e.point(2, 0) # generator of the order-8 group
		chain = [e.infinity]
		7.times {chain << chain.last + g}
		8.times {|k| assert_equal(chain[k], k * g)}
		8.times {|k| assert_equal(chain[k], g * k)}
		assert_equal(e.infinity, 8 * g)
		# Negative scalar: (-k)P = -(kP).
		assert_equal(-(3 * g), (-3) * g)
	end

	def test_scalar_mult_gf8
		e = EC2_poly_mod_curve.new(0, 1, F8) # order 4
		p = e.point(1, 0)
		assert_equal(e.point(0, 1), 2 * p)
		assert_equal(e.infinity, 4 * p)
	end

	def test_trace
		e = EC2_poly_mod_curve.new(0, 1, F8)
		assert_equal(1, e.trace(1))
		assert_equal(0, e.trace(2))
		assert_equal(1, e.trace(3))
		assert_equal(0, e.trace(0))
	end

	def test_compress_roundtrip_all_points
		[[F4, 0x7, 1, 1], [F8, 0xb, 0, 1], [F8, 0xb, 1, 1]].each do |f, ff, a, b|
			e = EC2_poly_mod_curve.new(a, b, ff)
			assert_equal("O", e.infinity.compress)
			assert_equal(e.infinity, e.decompress("O"))
			e.points.each do |p|
				c = p.compress
				q = e.decompress(c)
				assert_equal(p, q, "roundtrip #{e.inspect}: #{c}")
				if p.x.zero?
					assert_match(/\A00:/, c) # full y stored for x = 0
				else
					assert_match(/:[01]\z/, c) # beta bit only
				end
			end
		end
	end

	def test_compress_x0
		e = EC2_poly_mod_curve.new(1, 1, F4)
		t = e.point(0, 1)
		assert_equal("00:1", t.compress)
		assert_equal(t, e.decompress("00:1"))
		# Malformed or off-curve x = 0 payloads.
		assert_raise(RuntimeError) {e.decompress("00:0")}
		assert_raise(RuntimeError) {e.decompress("nonsense")}
		assert_raise(RuntimeError) {e.decompress("1:2")} # bad beta bit
	end

	def test_decompress_no_solution
		# GF(8), E: y^2+xy = x^3 + 1.  Pick an x with
		# Tr(x + b/x^2) = 1, i.e. no points with that x.
		e = EC2_poly_mod_curve.new(0, 1, F8)
		found = false
		F2_poly_mod.elements_for_modulus(F8).each do |x|
			next if x.zero?
			rhs = x + e.b / (x*x)
			if e.trace(rhs) == 1
				assert_nil(e.roots_for_x(x))
				assert_nil(e.decompress("#{x.residue.bits.to_s(16)}:0"))
				assert_raise(RuntimeError) do
					e.decompress!("#{x.residue.bits.to_s(16)}:0")
				end
				found = true
			end
		end
		assert(found, "expected at least one unsolvable x on this curve")
	end

	def test_decompress_picks_correct_beta_root
		e = EC2_poly_mod_curve.new(0, 1, F4)
		p0 = e.decompress("1:0")
		p1 = e.decompress("1:1")
		assert_not_nil(p0)
		assert_not_nil(p1)
		assert_equal(F2_poly_mod.new(1, F4), p0.x)
		assert_equal(F2_poly_mod.new(1, F4), p1.x)
		assert_not_equal(p0, p1)
		assert_equal(p0, -p1) # the two roots are paired under negation
		assert_equal(p0, e.decompress(p0.compress))
		assert_equal(p1, e.decompress(p1.compress))
	end

end

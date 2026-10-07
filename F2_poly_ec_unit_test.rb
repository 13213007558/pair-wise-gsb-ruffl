#!/usr/bin/ruby -Wall

require 'F2_poly_ec.rb'
require 'test/unit'

class F2_poly_ec_unit_test < Test::Unit::TestCase

	def test_curve_construction_and_point_validation
		curve = F2_poly_ec.new(0, 1, 0xb)
		assert_equal(F2_poly_ec.new(0, 1, 0xb), curve)
		assert_equal(curve.hash, F2_poly_ec.new(0, 1, 0xb).hash)
		assert_equal(true, curve.on_curve?(0, 1))
		assert_equal(true, curve.on_curve?(1, 0))
		assert_equal(false, curve.on_curve?(1, 2))
		assert_raise(RuntimeError) {curve.point(1, 2)}
		assert_raise(RuntimeError) {F2_poly_ec.new(0, 0, 0xb)}
		assert_raise(RuntimeError) {F2_poly_ec.new(0, 1, 5)}
	end

	def test_enumerated_f8_group_law
		curve = F2_poly_ec.new(0, 1, 0xb)
		points = curve.points
		infinity = curve.infinity
		order_two = curve.point(0, 1)
		generator = curve.point(1, 0)
		generator_inverse = curve.point(1, 1)

		assert_equal([
			infinity,
			order_two,
			generator,
			generator_inverse
		], points)
		assert_equal(4, points.size)

		points.each do |point|
			assert_equal(point, infinity + point)
			assert_equal(point, point + infinity)
			assert_equal(infinity, point + (-point))
		end

		assert_equal(infinity, order_two.double)
		assert_equal(order_two, -order_two)
		assert_equal(generator_inverse, -generator)
		assert_equal(order_two, generator.double)
		assert_equal(generator_inverse, generator.double + generator)
		assert_equal(infinity, 4 * generator)

		points.product(points).each do |left, right|
			assert_equal(right + left, left + right)
			assert(points.include?(left + right))
		end

		points.product(points, points).each do |left, middle|
			points.each do |right|
				assert_equal(
					left + (middle + right),
					(left + middle) + right
				)
			end
		end
	end

	def test_scalar_multiplication
		curve = F2_poly_ec.new(0, 1, 0xb)
		generator = curve.point(1, 0)
		infinity = curve.infinity

		assert_equal(infinity, generator * 0)
		assert_equal(generator, generator * 1)
		assert_equal(curve.point(0, 1), generator * 2)
		assert_equal(curve.point(1, 1), generator * 3)
		assert_equal(infinity, generator * 4)
		assert_equal(curve.point(1, 1), generator * -1)
		assert_equal(curve.point(1, 1), -1 * generator)
		assert_raise(RuntimeError) {generator * 1.5}
	end

	def test_f4_compression_and_both_roots
		curve = F2_poly_ec.new(0, 1, 7)
		curve.points.each do |point|
			assert_equal(point, curve.decompress(point.compress))
			assert_equal(point, curve.read_compressed(point.write_compressed))
		end

		assert_equal("00", curve.infinity.compress)
		assert_equal("030", curve.point(0, 1).write_compressed)
		assert_equal("022", curve.point(2, 0).compress)
		assert_equal("032", curve.point(2, 2).compress)
		assert_equal("023", curve.point(3, 0).compress)
		assert_equal("033", curve.point(3, 3).compress)

		assert_equal(curve.point(2, 0), curve.decompress("022"))
		assert_equal(curve.point(2, 2), curve.decompress("032"))
	end

	def test_f8_compression_edge_cases
		curve = F2_poly_ec.new(0, 1, 0xb)
		x_zero = curve.point(0, 1)

		assert_equal("030", x_zero.write_compressed)
		assert_equal(x_zero, curve.read_compressed("030"))
		assert_equal(x_zero, curve.read_compressed("020"))
		assert_raise(RuntimeError) {curve.decompress("022")}
		assert_raise(RuntimeError) {curve.decompress("032")}
		assert_raise(RuntimeError) {curve.decompress("028")}
		assert_raise(RuntimeError) {curve.decompress("421")}
		assert_raise(RuntimeError) {curve.decompress("0210")}
		assert_raise(RuntimeError) {curve.decompress(123)}
	end

	def test_f8_general_curve_parameter
		curve = F2_poly_ec.new(1, 1, 0xb)
		points = curve.points
		generator = curve.point(2, 5)

		assert_equal(14, points.size)
		assert_equal(curve.infinity, generator * 14)
		points.each do |point|
			assert_equal(point, curve.decompress(point.compress))
			assert_equal(curve.infinity, point + (-point))
		end
	end

	def test_f16_even_extension_group_order
		curve = F2_poly_ec.new(1, 1, 0x13)
		points = curve.points

		assert_equal(16, points.size)
		points.each do |point|
			assert_equal(point, curve.decompress(point.compress))
			assert_equal(curve.infinity, point * points.size)
			assert_equal(-point, point * (points.size - 1))
		end
	end

end

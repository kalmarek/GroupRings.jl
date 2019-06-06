using Test
using AbstractAlgebra

has_base_ring(R::AbstractAlgebra.NCRing) = base_ring(R) != Union{}

function test_data_type(f,g)
    @testset "Data type" begin
        f,g = deepcopy(f), deepcopy(g)

        if f isa NCRingElem
            @test parent(f) isa AbstractAlgebra.NCRing
        else
            @test parent(f) isa AbstractAlgebra.Ring
        end

        R = parent(f)
        @test typeof(R) <: parent_type(typeof(f))
        @test typeof(f) <: elem_type(typeof(R))

        @test base_ring(R) isa AbstractAlgebra.Ring || base_ring(R) == Union{}

        if f isa RingElement
            @test isdomain_type(typeof(f)) isa Bool
        end
        @test isexact_type(typeof(f)) isa Bool

        @test deepcopy(f) isa typeof(f)
        @test !(deepcopy(f) === f)
        @test parent(deepcopy(f)) === parent(f)

        @test hash(f, UInt(0)) isa UInt
        @test hash(deepcopy(f)) == hash(f)
    end
end

function test_constructors(f,g)
    @testset "Constructors" begin
        f,g = deepcopy(f), deepcopy(g)
        R = parent(f)

        @test R() isa typeof(f)
        @test R(0) isa typeof(f)
        @test R(Int16(0)) isa typeof(f)
        @test R(big(1)) isa typeof(f)
        @test zero(R) isa typeof(f)
        @test one(R) isa typeof(f)

        # no copy constructor
        @test R(f) === f

        if has_base_ring(R)
            S = base_ring(R)
            @test R(S(0)) isa typeof(f)
            @test R(S(1)) isa typeof(f)
        end

        @test iszero(R(0))
        @test !iszero(R(1))
        @test isone(R(1))
        @test !isone(R(0))
        @test !(iszero(f) && isone(f))

        if f isa RingElement
            @test canonical_unit(f) isa typeof(f)

            @test canonical_unit(f)*canonical_unit(g) == canonical_unit(f * g)
            if f isa FieldElement
                @test canonical_unit(f) === f
            end
        end
    end
end

function test_string_io(f,g)
    f,g = deepcopy(f), deepcopy(g)
    @testset "String I/O" begin
        # these go through show unless string() is defined
        @test string(f) isa String
        @test string(parent(f)) isa String

        @test needs_parentheses(f) isa Bool
        @test displayed_with_minus_in_front(f) isa Bool
        @test show_minus_one(typeof(f)) isa Bool
    end
end

function test_comparison(f,g)
    f,g = deepcopy(f), deepcopy(g)
    @testset "Comparison" begin
        R = parent(f)

        @test R(0) == R()
        @test R(Int16(0)) == R()
        @test zero(R) == R(0)
        @test one(R) == R(1)

        @test f == f
        @test g == g
        @test (f == g) isa Bool

        @test isequal(f,g) isa Bool
        @test isequal(R(0), R())
        @test isequal(R(1), one(R))
        @test isequal(f,f)
        @test isequal(g,g)

        if !isexact_type(typeof(f))
            @test isapprox(f, f; atol=1e-12) isa Bool
            if has_base_ring(R)
                S = base_ring(R)
                @test isapprox(f, S(1); atol=1e-12) isa Bool
                @test isapprox(S(1), f; atol=1e-12) isa Bool
            end
        end
    end
end

function test_unary_binary_ops(f,g)
    f,g = deepcopy(f), deepcopy(g)
    @testset "Unary/binary operators" begin
        R = parent(f)

        # check that operations have no side effects:
        old_f, old_g = deepcopy(f), deepcopy(g)
        @test parent(-f) == parent(f)
        @test !(-f === f)
        @test f == old_f

        @test f+g isa typeof(f)
        @test parent(f) == parent(f+g)
        @test !(f+g === f) && !(f+g === g)
        @test f == old_f && g == old_g

        @test f-g isa typeof(f)
        @test parent(f) == parent(f-g)
        @test !(f-g === f) && !(f-g === g)
        @test f == old_f && g == old_g

        @test f*g isa typeof(f)
        @test parent(f) == parent(f*g)
        @test !(f*g === f) && !(f*g === g)
        @test f == old_f && g == old_g

        # unary minus
        @test -f isa typeof(f)
        @test -(-f) == f
        @test -R(1) == R(-1)
        @test -R(0) == R(0)

        # arithmetic binary ops
        @test f + g == g + f
        @test R(0) + R(1) == R(1)
        @test R(1) + R(1) == R(2)
        @test R(0) - R(1) == -R(1)
        @test f - f == -f + f == R(0)
        @test (f + g) + R(1) == g + (f + R(1))

        @test R(0) * R(1) == R(0)
        @test R(1) * f == f
        @test R(0) * f == R(0)
        @test f^2 == f * f
        @test f^5 == (f * f)^2 * f
        @test (f*g)^2 == f*g*f*g
    end
end

function test_divexact(f,g)
    f,g = deepcopy(f), deepcopy(g)
    @testset "divexact" begin
        R = parent(f)

        try
            divexact_left(g*f, f)
            @test divexact_left(g*f, f) == g
            if f isa RingElement && g isa RingElement
                @test divexact_left(g*f, g) == divexact_right(g*f, g)
            end
        catch DivideError
            nothing
        end

        try
            divexact_right(f*g, g)
            @test divexact_right(f*g, g) == f
            if f isa RingElement && g isa RingElement
                @test divexact_left(f*g, f) == divexact_right(g*f, f)
            end
        catch DivideError
            nothing
        end

        if f isa RingElement && g isa RingElement
            @test_throws DivideError divexact(f, R(0))
        end

        @test divexact_left(f, R(1)) == f
        @test divexact_right(g, R(1)) == g

        @test_throws DivideError divexact_left(f, R(0))
        @test_throws DivideError divexact_right(f, R(0))
    end
end

function test_unsafe_ops(f,g)
    f,g = deepcopy(f), deepcopy(g)

    @testset "unsafe operators" begin
        R = parent(f)
        let f = f, g = g
            t = deepcopy(f)

            @test zero!(t) == R(0)
            @test AbstractAlgebra.mul!(t, f, g) == f*g
            @test add!(t, f, g) == f+g
            @test addeq!(deepcopy(f), g) == f + g

            # the same but with aliasing:
            v = f * g
            @test AbstractAlgebra.mul!(f, f, g) == v
            v = f + g
            @test add!(f, f, g) == v
            v = f + g
            @test addeq!(f, g) == v
        end
    end
end

function test_promote_rules(f,g)
    f,g = deepcopy(f), deepcopy(g)
    @testset "promote_rules" begin

        function test_promotes(F::Type, I::Type)
            @testset "Promote_type with $I" begin
                @test AbstractAlgebra.promote_rule(F, I) isa Type
                @test AbstractAlgebra.promote_rule(F, I) != Union{}
                @test AbstractAlgebra.promote_rule(F, I) ==
                      AbstractAlgebra.promote_rule(I, F)
            end
        end

        test_promotes(typeof(f), Int16)
        test_promotes(typeof(f), BigInt)

        test_promotes(typeof(f), typeof(g))
        @test AbstractAlgebra.promote_rule(typeof(f), typeof(g)) == typeof(f)

        if has_base_ring(parent(f))
            S = base_ring(parent(f))
            test_promotes(typeof(f), elem_type(S))
            @test AbstractAlgebra.promote_rule(typeof(f), elem_type(S)) == typeof(f)
        end
    end
end

function test_optional_functionality(f,g)
    f,g = deepcopy(f), deepcopy(g)

    function test_pmt(f,x, T=typeof(f))
        @test f+x isa T
        @test x+f isa T
        @test f-x isa T
        @test x-f isa T
        @test f*x isa T
        @test x*f isa T
    end


    @testset "Optional functionality" begin
        R = parent(f)

        @test R(1) == 1
        @test 0 == R(0)

        test_pmt(f, 2, typeof(f))

        if has_base_ring(R)
            S = base_ring(R)
            test_pmt(f, S(2), typeof(f))

            @test R(1) == S(1)
            @test S(0) == R(0)
        end

        try
            divexact(f, 1)
            @test divexact(f, 1) == f
        catch MethodError
            nothing
        end

        try
            isunit(f)
            @test isunit(f) isa Bool
        catch MethodError
            nothing
        end

        try
            f^big(2)
            @test f^big(2) == f^2
        catch MethodError
            nothing
        end

        try
            addmul!(r, f, g, R(0))

            r = R(1)
            @test addmul!(r, f, g, R(0)) == 1 + f * g
            @test r == 1 + f*g

            v = deepcopy(f)
            @test addmul!(f, f, g, R(0)) == v + v * g
            @test f == v + v*g

        catch MethodError
            nothing
        end
    end
end


function test_ringinterface(f, g)
    @testset "Ring Interface" begin

        test_data_type(f,g)
        test_constructors(f,g)
        test_string_io(f,g)
        test_comparison(f,g)
        test_unary_binary_ops(f,g)
        test_divexact(f,g)
        test_unsafe_ops(f,g)
        test_promote_rules(f,g)

        @testset "rand" begin
            # ???
        end
        test_optional_functionality(f,g)
    end
end

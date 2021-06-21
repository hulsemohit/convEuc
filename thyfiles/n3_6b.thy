theory n3_6b
	imports Axioms Definitions Theorems
begin

theorem n3_6b:
	assumes: `axioms`
		"bet A B C"
		"bet A C D"
	shows: "bet A B D"
proof -
	have "bet C B A" using betweennesssymmetryE[OF `axioms` `bet A B C`] .
	have "bet D C A" using betweennesssymmetryE[OF `axioms` `bet A C D`] .
	have "bet D B A" using n3_5b[OF `axioms` `bet D C A` `bet C B A`] .
	have "bet A B D" using betweennesssymmetryE[OF `axioms` `bet D B A`] .
	thus ?thesis by blast
qed
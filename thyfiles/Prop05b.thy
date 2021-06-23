theory Prop05b
	imports Geometry Prop05 collinearorder equalanglesNC inequalitysymmetric ray4 supplements
begin

theorem Prop05b:
	assumes "axioms"
		"tri_isos A B C"
		"bet A B F"
		"bet A C G"
	shows "ang_eq C B F B C G"
proof -
	have "ang_eq A B C A C B" using Prop05[OF `axioms` `tri_isos A B C`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "\<not> col A C B" using equalanglesNC[OF `axioms` `ang_eq A B C A C B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		have "col A C B" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col A C B` `\<not> col A C B` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "bet A B F \<and> ray_on B C C" using `bet A B F` `ray_on B C C` by blast
	have "supplement A B C C F" using supplement_b[OF `axioms` `ray_on B C C` `bet A B F`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "ray_on C B B \<and> bet A C G" using `ray_on C B B` `bet A C G` by blast
	have "supplement A C B B G" using supplement_b[OF `axioms` `ray_on C B B` `bet A C G`] .
	have "ang_eq C B F B C G" using supplements[OF `axioms` `ang_eq A B C A C B` `supplement A B C C F` `supplement A C B B G`] .
	thus ?thesis by blast
qed

end
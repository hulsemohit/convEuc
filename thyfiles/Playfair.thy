theory Playfair
	imports Axioms Definitions Theorems
begin

theorem Playfair:
	assumes: `axioms`
		"parallel A B C D"
		"parallel A B C E"
	shows: "col C D E"
proof -
	have "cross A D B C \<or> cross A C B D"
	proof (rule ccontr)
		assume "\<not> (cross A D B C \<or> cross A C B D)"
		have "\<not> (cross A D B C) \<and> \<not> (cross A C B D)" sorry
		have "\<not> (cross A D B C)" using `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by simp
		have "\<not> (cross A C B D)" using `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by simp
		have "parallel A B D C" using parallelflip[OF `axioms` `parallel A B C D`] by blast
		have "cross A C D B" using crisscross[OF `axioms` `parallel A B D C` `\<not> (cross A D B C)`] .
		obtain p where "bet A p C \<and> bet D p B" sorry
		have "bet A p C" using `bet A p C \<and> bet D p B` by simp
		have "bet D p B" using `bet A p C \<and> bet D p B` by simp
		have "bet B p D" using betweennesssymmetryE[OF `axioms` `bet D p B`] .
		have "bet A p C \<and> bet B p D"  using `bet A p C` `bet B p D` by simp
		have "cross A C B D" sorry
		show "False" sorry
	qed
	hence "cross A D B C \<or> cross A C B D" by blast

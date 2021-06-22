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
		have "\<not> (cross A D B C) \<and> \<not> (cross A C B D)" using `\<not> (cross A D B C \<or> cross A C B D)` by blast
		have "\<not> (cross A D B C)" using `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by blast
		have "\<not> (cross A C B D)" using `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by blast
		have "parallel A B D C" using parallelflip[OF `axioms` `parallel A B C D`] by blast
		have "cross A C D B" using crisscross[OF `axioms` `parallel A B D C` `\<not> (cross A D B C)`] .
		obtain p where "bet A p C \<and> bet D p B" sorry
		have "bet A p C" using `bet A p C \<and> bet D p B` by blast
		have "bet D p B" using `bet A p C \<and> bet D p B` by blast
		have "bet B p D" using betweennesssymmetryE[OF `axioms` `bet D p B`] .
		have "bet A p C \<and> bet B p D" using `bet A p C \<and> bet D p B` `bet B p D` by blast
		have "cross A C B D" sorry
		show "False" using `cross A C B D` `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by blast
	qed
	hence "cross A D B C \<or> cross A C B D" by blast
	consider "cross A D B C"|"cross A C B D" using `cross A D B C \<or> cross A C B D`  by blast
	hence col C D E
	proof (cases)
		case 1
		have "col C D E" using Playfairhelper2[OF `axioms` `parallel A B C D` `parallel A B C E` `cross A D B C`] .
	next
		case 2
		obtain p where "bet A p C \<and> bet B p D" sorry
		have "bet A p C" using `bet A p C \<and> bet B p D` by blast
		have "bet B p D" using `bet A p C \<and> bet B p D` by blast
		have "bet B p D \<and> bet A p C" using `bet A p C \<and> bet B p D` `bet A p C \<and> bet B p D` by blast
		have "cross B D A C" sorry
		have "parallel B A C D" using parallelflip[OF `axioms` `parallel A B C D`] by blast
		have "parallel B A C E" using parallelflip[OF `axioms` `parallel A B C E`] by blast
		have "col C D E" using Playfairhelper2[OF `axioms` `parallel B A C D` `parallel B A C E` `cross B D A C`] .
	next
	thus ?thesis by blast
qed

end
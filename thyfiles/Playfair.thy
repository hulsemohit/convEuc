theory Playfair
	imports Geometry Playfairhelper2 crisscross parallelflip
begin

theorem(in euclidean_geometry) Playfair:
	assumes 
		"parallel A B C D"
		"parallel A B C E"
	shows "col C D E"
proof -
	have "\<not> (\<not> (cross A D B C \<or> cross A C B D))"
	proof (rule ccontr)
		assume "\<not> (\<not> (\<not> (cross A D B C \<or> cross A C B D)))"
hence "\<not> (cross A D B C \<or> cross A C B D)" by blast
		have "\<not> (cross A D B C) \<and> \<not> (cross A C B D)" using `\<not> (cross A D B C \<or> cross A C B D)` by blast
		have "\<not> (cross A D B C)" using `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by blast
		have "\<not> (cross A C B D)" using `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by blast
		have "parallel A B D C" using parallelflip[OF `parallel A B C D`] by blast
		have "cross A C D B" using crisscross[OF `parallel A B D C` `\<not> (cross A D B C)`] .
		obtain p where "bet A p C \<and> bet D p B" using cross_f[OF `cross A C D B`]  by  blast
		have "bet A p C" using `bet A p C \<and> bet D p B` by blast
		have "bet D p B" using `bet A p C \<and> bet D p B` by blast
		have "bet B p D" using betweennesssymmetryE[OF `bet D p B`] .
		have "bet A p C \<and> bet B p D" using `bet A p C \<and> bet D p B` `bet B p D` by blast
		have "cross A C B D" using cross_b[OF `bet A p C` `bet B p D`] .
		show "False" using `cross A C B D` `\<not> (cross A D B C) \<and> \<not> (cross A C B D)` by blast
	qed
	hence "cross A D B C \<or> cross A C B D" by blast
	consider "cross A D B C"|"cross A C B D" using `\<not> (\<not> (cross A D B C \<or> cross A C B D))`  by blast
	hence "col C D E"
	proof (cases)
		assume "cross A D B C"
		have "col C D E" using Playfairhelper2[OF `parallel A B C D` `parallel A B C E` `cross A D B C`] .
		thus ?thesis by blast
	next
		assume "cross A C B D"
		obtain p where "bet A p C \<and> bet B p D" using cross_f[OF `cross A C B D`]  by  blast
		have "bet A p C" using `bet A p C \<and> bet B p D` by blast
		have "bet B p D" using `bet A p C \<and> bet B p D` by blast
		have "bet B p D \<and> bet A p C" using `bet A p C \<and> bet B p D` `bet A p C \<and> bet B p D` by blast
		have "cross B D A C" using cross_b[OF `bet B p D` `bet A p C`] .
		have "parallel B A C D" using parallelflip[OF `parallel A B C D`] by blast
		have "parallel B A C E" using parallelflip[OF `parallel A B C E`] by blast
		have "col C D E" using Playfairhelper2[OF `parallel B A C D` `parallel B A C E` `cross B D A C`] .
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end
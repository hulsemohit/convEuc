theory Playfairhelper2
	imports Axioms Definitions Theorems
begin

theorem Playfairhelper2:
	assumes: `axioms`
		"parallel A B C D"
		"parallel A B C E"
		"cross A D B C"
	shows: "col C D E"
proof -
	have "A \<noteq> B" using parallel_f[OF `axioms` `parallel A B C D`] by blast
	have "cross A E B C \<or> cross A C E B"
	proof (rule ccontr)
		assume "\<not> (cross A E B C \<or> cross A C E B)"
		have "\<not> (cross A E B C) \<and> \<not> (cross A C E B)" using `\<not> (cross A E B C \<or> cross A C E B)` by blast
		have "\<not> (cross A E B C)" using `\<not> (cross A E B C) \<and> \<not> (cross A C E B)` by blast
		have "\<not> (cross A C E B)" using `\<not> (cross A E B C) \<and> \<not> (cross A C E B)` by blast
		have "parallel A B E C" using parallelflip[OF `axioms` `parallel A B C E`] by blast
		have "cross A C E B" using crisscross[OF `axioms` `parallel A B E C` `\<not> (cross A E B C)`] .
		show "False" using `cross A C E B` `\<not> (cross A E B C) \<and> \<not> (cross A C E B)` by blast
	qed
	hence "cross A E B C \<or> cross A C E B" by blast
	obtain M where "bet A M D \<and> bet B M C" using cross_f[OF `axioms` `cross A D B C`] by blast
	have "bet B M C" using `bet A M D \<and> bet B M C` by blast
	consider "cross A E B C"|"cross A C E B" using `cross A E B C \<or> cross A C E B`  by blast
	hence col C D E
	proof (cases)
		case 1
		have "col C D E" using Playfairhelper[OF `axioms` `parallel A B C D` `parallel A B C E` `cross A D B C` `cross A E B C`] .
	next
		case 2
		obtain m where "bet A m C \<and> bet E m B" using cross_f[OF `axioms` `cross A C E B`] by blast
		have "bet A m C" using `bet A m C \<and> bet E m B` by blast
		have "bet E m B" using `bet A m C \<and> bet E m B` by blast
		have "C \<noteq> E" using parallel_f[OF `axioms` `parallel A B C D`] by blast
		have "E \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> E`] .
		have "bet E C e \<and> seg_eq C e E C" using extensionE[OF `axioms` `E \<noteq> C` `E \<noteq> C`] by blast
		have "bet E C e" using `bet E C e \<and> seg_eq C e E C` by blast
		have "col E C e" using collinear_b `axioms` `bet E C e \<and> seg_eq C e E C` by blast
		have "C \<noteq> e" using betweennotequal[OF `axioms` `bet E C e`] by blast
		have "e \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> e`] .
		have "parallel A B E C" using parallelflip[OF `axioms` `parallel A B C E`] by blast
		have "parallel A B e C" using collinearparallel[OF `axioms` `parallel A B E C` `col E C e` `e \<noteq> C`] .
		have "parallel A B C e" using parallelflip[OF `axioms` `parallel A B e C`] by blast
		have "\<not> col A B C" using parallelNC[OF `axioms` `parallel A B C D`] by blast
		have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
		obtain H where "bet B H m \<and> bet A H M" using Pasch-innerE[OF `axioms` `bet B M C` `bet A m C` `\<not> col B C A`] by blast
		have "\<not> col A E C" using parallelNC[OF `axioms` `parallel A B E C`] by blast
		have "col E C e" using collinear_b `axioms` `bet E C e \<and> seg_eq C e E C` by blast
		have "col C E e" using collinearorder[OF `axioms` `col E C e`] by blast
		have "\<not> col C E A" using NCorder[OF `axioms` `\<not> col A E C`] by blast
		have "E = E" using equalityreflexiveE[OF `axioms`] .
		have "col C E E" using collinear_b `axioms` `E = E` by blast
		have "E \<noteq> e" using betweennotequal[OF `axioms` `bet E C e`] by blast
		have "\<not> col E e A" using NChelper[OF `axioms` `\<not> col C E A` `col C E E` `col C E e` `E \<noteq> e`] .
		have "bet A m C" using `bet A m C` .
		have "bet E C e" using `bet E C e` .
		obtain F where "bet A F e \<and> bet E m F" using Pasch-outerE[OF `axioms` `bet A m C` `bet E C e` `\<not> col E e A`] by blast
		have "bet A F e" using `bet A F e \<and> bet E m F` by blast
		have "bet E m F" using `bet A F e \<and> bet E m F` by blast
		have "bet e F A" using betweennesssymmetryE[OF `axioms` `bet A F e`] .
		have "col E m F" using collinear_b `axioms` `bet A F e \<and> bet E m F` by blast
		have "col E m B" using collinear_b `axioms` `bet A m C \<and> bet E m B` by blast
		have "col m E F" using collinearorder[OF `axioms` `col E m F`] by blast
		have "col m E B" using collinearorder[OF `axioms` `col E m B`] by blast
		have "E \<noteq> m" using betweennotequal[OF `axioms` `bet E m B`] by blast
		have "m \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> m`] .
		have "col E F B" using collinear4[OF `axioms` `col m E F` `col m E B` `m \<noteq> E`] .
		have "col E B F" using collinearorder[OF `axioms` `col E F B`] by blast
		have "e \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> e`] .
		have "bet e F A" using `bet e F A` .
		have "E = E" using equalityreflexiveE[OF `axioms`] .
		have "col e E E" using collinear_b `axioms` `E = E` by blast
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		have "col B B A" using collinear_b `axioms` `B = B` by blast
		have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
		have "parallel A B E C" using `parallel A B E C` .
		have "parallel A B C E" using parallelflip[OF `axioms` `parallel A B E C`] by blast
		have "col E C e" using `col E C e` .
		have "col C E e" using collinearorder[OF `axioms` `col E C e`] by blast
		have "E \<noteq> e" using `E \<noteq> e` .
		have "parallel A B e E" using collinearparallel[OF `axioms` `parallel A B C E` `col C E e` `e \<noteq> E`] .
		have "parallel e E A B" using parallelsymmetric[OF `axioms` `parallel A B e E`] .
		have "parallel e E B A" using parallelflip[OF `axioms` `parallel e E A B`] by blast
		have "\<not> (meets e E B A)" using parallel_f[OF `axioms` `parallel e E B A`] by blast
		have "bet E F B" using collinearbetween[OF `axioms` `col e E E` `col B B A` `e \<noteq> E` `B \<noteq> A` `e \<noteq> E` `B \<noteq> A` `\<not> (meets e E B A)` `bet e F A` `col E B F`] .
		have "bet B F E" using betweennesssymmetryE[OF `axioms` `bet E F B`] .
		have "bet e C E" using betweennesssymmetryE[OF `axioms` `bet E C e`] .
		have "\<not> col B E C" using parallelNC[OF `axioms` `parallel A B E C`] by blast
		have "\<not> col E C B" using NCorder[OF `axioms` `\<not> col B E C`] by blast
		have "col E C e" using collinear_b `axioms` `bet E C e \<and> seg_eq C e E C` by blast
		have "E = E" using equalityreflexiveE[OF `axioms`] .
		have "col E C E" using collinear_b `axioms` `E = E` by blast
		have "\<not> col E e B" using NChelper[OF `axioms` `\<not> col E C B` `col E C E` `col E C e` `E \<noteq> e`] .
		have "\<not> col B E e" using NCorder[OF `axioms` `\<not> col E e B`] by blast
		obtain K where "bet B K C \<and> bet e K F" using Pasch-innerE[OF `axioms` `bet B F E` `bet e C E` `\<not> col B E e`] by blast
		have "bet B K C" using `bet B K C \<and> bet e K F` by blast
		have "bet e K F" using `bet B K C \<and> bet e K F` by blast
		have "bet e F A" using betweennesssymmetryE[OF `axioms` `bet A F e`] .
		have "bet e K A" using n3_6b[OF `axioms` `bet e K F` `bet e F A`] .
		have "bet A K e" using betweennesssymmetryE[OF `axioms` `bet e K A`] .
		have "bet A K e" using `bet A K e` .
		have "bet B K C" using `bet B K C` .
		have "bet A K e \<and> bet B K C" using `bet A K e` `bet B K C \<and> bet e K F` by blast
		have "cross A e B C" using cross_b[OF `axioms` `bet A K e` `bet B K C`] .
		have "col C D e" using Playfairhelper[OF `axioms` `parallel A B C D` `parallel A B C e` `cross A D B C` `cross A e B C`] .
		have "col e C D" using collinearorder[OF `axioms` `col C D e`] by blast
		have "col e C E" using collinearorder[OF `axioms` `col C E e`] by blast
		have "C \<noteq> e" using betweennotequal[OF `axioms` `bet E C e`] by blast
		have "e \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> e`] .
		have "col C D E" using collinear4[OF `axioms` `col e C D` `col e C E` `e \<noteq> C`] .
	next
	thus ?thesis by blast
qed

end
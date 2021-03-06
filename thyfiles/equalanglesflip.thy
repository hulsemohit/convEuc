theory equalanglesflip
	imports ABCequalsCBA Geometry collinearorder equalanglesNC equalanglessymmetric equalanglestransitive
begin

theorem(in euclidean_geometry) equalanglesflip:
	assumes 
		"ang_eq A B C D E F"
	shows "ang_eq C B A F E D"
proof -
	have "\<not> col D E F" using equalanglesNC[OF `ang_eq A B C D E F`] .
	have "ang_eq D E F A B C" using equalanglessymmetric[OF `ang_eq A B C D E F`] .
	have "\<not> col A B C" using equalanglesNC[OF `ang_eq D E F A B C`] .
	have "\<not> (col C B A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C B A))"
hence "col C B A" by blast
		have "col A B C" using collinearorder[OF `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C B A" by blast
	have "ang_eq C B A A B C" using ABCequalsCBA[OF `\<not> col C B A`] .
	have "ang_eq C B A D E F" using equalanglestransitive[OF `ang_eq C B A A B C` `ang_eq A B C D E F`] .
	have "ang_eq D E F F E D" using ABCequalsCBA[OF `\<not> col D E F`] .
	have "ang_eq C B A F E D" using equalanglestransitive[OF `ang_eq C B A D E F` `ang_eq D E F F E D`] .
	thus ?thesis by blast
qed

end
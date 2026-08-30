add_cus_dep('slo', 'sls', 1, 'makeglossaries');
add_cus_dep('glo', 'gls', 1, 'makeglossaries');
add_cus_dep('acn', 'acr', 1, 'makeglossaries');
$generated_exts = [@generated_exts, qw(glo gls acn acr slg slo sls xdy)];
$clean_ext .= ' glo gls acn acr slg slo sls xdy';

sub makeglossaries {
    my ($base, $path) = fileparse($_[0]);
    pushd($path);
    system("makeglossaries $base");
    popd;
    return;
}

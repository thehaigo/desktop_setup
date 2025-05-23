{application, public_key,
  [{description, "Public key infrastructure"},
   {vsn, "1.15.1"},
   {modules, [public_key,
              pubkey_pem,
              pubkey_pbe,
              pubkey_ssh,
              pubkey_cert,
              pubkey_policy_tree,
              pubkey_cert_records,
              pubkey_crl,
              pubkey_ocsp,
              pubkey_os_cacerts,
              'OTP-PUB-KEY',
              'PKCS-FRAME'
             ]},
   {applications, [asn1, crypto, kernel, stdlib]},
   {registered, []},
   {env, []},
   {runtime_dependencies, ["stdlib-3.5","kernel-3.0","erts-6.0","crypto-4.6",
			   "asn1-3.0"]}
  ]
}.


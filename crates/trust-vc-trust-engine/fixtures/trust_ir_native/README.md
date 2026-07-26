# Native TrustIr Bundle Fixtures

`native_request_trust_bundle.json` is copied from TrustIr's conformance corpus at
rev `08b2f9c85556c6016f983943195ccf68302d7458`.

It pins direct TrustVc consumption of `trust_ir::NativeVerificationBundle` and its
typed `NativeVerificationRequest::TrustVc` variant. The fixture intentionally
does not use adapter-name strings or source-text verifier payloads, and includes
schema-v3 compiler facts, native assertion ids, replay metadata, and typed
native evidence bundles.

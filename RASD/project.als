abstract sig Bool{}
sig True extends Bool{}
sig False extends Bool{}

sig Username{}

sig Password{}

sig Name{}

sig Surname{}

sig AuthenticatorID{}

sig FiscalCode{}

sig City{
    position : one Position
}

sig Address{}

sig PhoneNumber{}

sig ID{}

sig Email{}

sig CertifiedEmail extends Email{}

sig DigitalCertificateX509{
    creationDate : one Date,
    dateOfExpiry : one Date,
    id : one ID
} {creationDate!=dateOfExpiry}

sig ViolationType{}

sig LicensePlateRecognizer{
    prefixLength: one Int,
    middleLength: one Int,
    suffixLength: one Int,
}{prefixLength=2 and middleLength=3 and suffixLength=2}

sig LicensePlate{
    licensePlateRecognizer : one LicensePlateRecognizer,
    modified : one Bool
}

sig Position{}

sig Note{
    length : one Int
}{length =< 140 && length > 0}

sig Image {
    accepted : one Bool
}

sig Date{}

abstract sig AuthentiaticationType {}
sig SPIDAuthentication extends AuthentiaticationType {}
sig ProprietaryAuthentication extends AuthentiaticationType {}

sig Authentication {
    authenticationType : one AuthentiaticationType,
    username : one Username,
    password : one Password
}

abstract sig User {
    name : one Name,
    surname : one Surname,
    autheticatorID : one AuthenticatorID,
    authentication : one Authentication,
    reportsMade : set Violation,
    email : one Email
}

sig NormalUser extends User {
    reliabilityScore : one Int,
    birthDate : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one City,
    phoneNumber : one PhoneNumber,
    city : one City,
    address : one Address
}

sig Authority extends User {
    authorization : one DigitalCertificateX509,
    notification: set Violation
}

sig VehicleType{}

sig Violation{
    violationID : one Int,
    violationType : some ViolationType,
    position : one Position,
    timeStamp : one Date,
    vehicleType: one VehicleType,
    image : one Image,
    licensePlate : one LicensePlate,
    note : one Note,
    email : one Email,
    autheticatorID : one AuthenticatorID,
    verified : one Bool
}{#violationType =< 3}

sig Map{}

abstract sig ViolationVisualizer{
    map : one Map,
    violation : some Violation
}
sig ViolationVisualizerLimited extends ViolationVisualizer{}
sig ViolationVisualizerPro extends ViolationVisualizer{}

sig Data{}

sig MunicipalityData {
    incidents : some Data
}

--represents Municiplality_i
sig Municipality {
    city : one City,
    municipalityData : one MunicipalityData
}

sig SuggestionsType {}

sig SuggestionInferralEngine {
    suggestions : some SuggestionsType,
    municipalities : set Municipality
}

fact noDuplicateUser {
    all u1, u2 : User | u1 = u2 iff u1.autheticatorID = u2.autheticatorID
}

fact noDuplicateUsername{
    all u1, u2: User | u1.autheticatorID = u2.autheticatorID
        iff u1.authentication.username = u2.authentication.username
}

fact noDuplicatePassword{
    all u1, u2: User | u1.authentication.username = u2.authentication.username
        iff u1.authentication.password = u2.authentication.password
}

fact noDuplicatePerson {
    all u1, u2 : User | u1.autheticatorID != u2.autheticatorID
        implies (u1.fiscalCode != u2.fiscalCode and u1.email != u2.email)
}

fact noDuplicatePhoneNumber{
    no u1, u2 : NormalUser | u1=u2 and u1.phoneNumber != u2.phoneNumber
}

fact emailAuthority {
    all u: User | u = Authority iff u.email = CertifiedEmail
}

fact noDuplicateAuthorization{
    no a1, a2 : Authorization | a1=a2 and a1.digitalCertificateX509 != a2.digitalCertificateX509
}

fact noDuplicateDigitalCertificateX509 {
    no c1, c2 : DigitalCertificateX509 | c1!=c2 and c1.id = c2.id
}

fact authorityUniqueCertificate{
    no a1, a2: Authority | a1=a2 and a1.authorization!=a2.authorization
}

fact noDuplicateViolationsFromAnUser {
    all v1, v2 : ViolationLimited | v1.autheticatorID = v2.autheticatorID
    implies (
        (v1.licensePlate != v2.licensePlate => (v1.timeStamp.milliseconds - v2.timeStamp.milliseconds < 1200000)) 
        and v1.position != v2.position
    )
}

fact noDuplicateViolationTypes {
    all vt, vt', vt'' : ViolationType, v: ViolationLimited | 
        ((#v.violationType=3 and vt in v.violationType and vt' in v.violationType and vt'' in v.violationType) 
            implies (vt != vt' and vt' != vt'' and vt != vt'')) or
        ((#v.violationType=2 and vt in v.violationType and vt' in v.violationType) => (vt != vt'))
}

fact reliabilityScoreInit {
    all u, u': User | (u!=u' and u.authentication.authenticationType = SPIDAuthentication
        and u'.authentication.authenticationType = ProprietaryAuthentication
        and #u.reportsMade = 0 and #u'.reportsMade = 0) implies (u.reliabilityScore > u'.reliabilityScore)
}

--notification
fact notificationFromUserToAuthority{
    all u: User | #u.reportsMade>0 iff (some a : Authority | let r = u.reportsMade | r in a.notification)
}

fact violationNotifier{
    all v: Violation, u : User | (v in u.reportsMade) implies (v.email = u.email)
}

fact statisticsVisualization{
    all u : User, v : ViolationVisualizer | (u = Authority and v.violationLimited = Violation)
        or u = NormalUser
}

fact statistics{
    all v : ViolationVisualizer | #v.violationLimited>0 iff (some u : User | #u.reportsMade>0)
}

fact suggestionsPossibile{
    all s : SuggestionInferralEngine | #s.suggestions>0 iff (some u : User | #u.reportsMade>0 and #s.suggestions.municipalityData>0)
}

fact providedDataFromMunicipality {
    all s: SuggestionInferred | #s.municipalityData>0 iff #s.municipalityData.data>0
}
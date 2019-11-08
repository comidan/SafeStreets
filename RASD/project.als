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
    city : one City,
    email : one Email
}

sig NormalUser extends User {
    reliabilityScore : one Int,
    birthDate : one Date,
    fiscalCode : one FiscalCode,
    birthLocation : one City,
    phoneNumber : one PhoneNumber,
    address : one Address
}

sig Authority extends User {
    authorization : one DigitalCertificateX509,
    notification : set Violation,
    suggestions : set SuggestionsType
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
}{#violationType =< 3 and violationID >= 0}

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

fact noDuplicatePassword{
    all u1, u2: User | u1.email = u2.email
        iff (u1.authentication.username = u2.authentication.username and u1.authentication.password = u2.authentication.password)
}

fact noDuplicatePerson {
    all u1, u2 : User | u1 = u2
        iff (u1.autheticatorID = u2.autheticatorID or u1.fiscalCode = u2.fiscalCode  or u1.email = u2.email
             or u1.authentication = u2.authentication or u1.phoneNumber = u2.phoneNumber)
}

fact emailAuthority {
    no u: User | u != Authority and u.email = CertifiedEmail
}

fact emailNormalUser {
	no u : User | u = NormalUser and u.email = CertifiedEmail
}

fact noDuplicateAuthorization{
    all a1, a2 : Authority | a1 = a2 implies a1.authorization = a2.authorization
}

fact noDuplicateDigitalCertificateX509 {
    all c1, c2 : DigitalCertificateX509 | c1 = c2 iff c1.id = c2.id
}

fact noDuplicateViolationsFromUser {
    all v1, v2 : Violation | v1.violationID = v2.violationID iff
    (v1.timeStamp = v2.timeStamp and v1.email = v2.email and v1.autheticatorID = v2.autheticatorID)
}

fact noDuplicateViolationID{
    all v1, v2 : Violation | v1 = v2 iff v1.violationID = v2.violationID
}

fact noDuplicateViolationTypes {
    all vt, vt', vt'' : ViolationType, v: Violation | 
        ((#v.violationType=3 and vt in v.violationType and vt' in v.violationType and vt'' in v.violationType) 
            implies (vt != vt' and vt' != vt'' and vt != vt'')) or
        ((#v.violationType=2 and vt in v.violationType and vt' in v.violationType) implies (vt != vt'))
}

fact reliabilityScoreInit {
    all u, u' : User | (u!=u' and u.authentication.authenticationType = SPIDAuthentication
        and u'.authentication.authenticationType = ProprietaryAuthentication
        and #u.reportsMade = 0 and #u'.reportsMade = 0) implies (u.reliabilityScore > u'.reliabilityScore)
}

fact verificationManagement{
    all v : Violation | v.verified = False iff v.verified != True
}

fact reliabilityScoreManagement {
    all u, u' : User | u = u' and (some x : Int | x > 0 and (u'.reliabilityScore = u.reliabilityScore + x)) iff
    (some v : Violation | v in u.reportsMade and v.verified = True)
}

--notification
fact notificationFromUserToAuthority{
    all u: User | #u.reportsMade>0 iff (some a : Authority | let r = u.reportsMade | r in a.notification)
}

fact violationNotifier{
    all v: Violation, u : User | (v in u.reportsMade) implies (v.email = u.email)
}

fact notifyWhomManagement{
    all u : User, a : Authority | let r = u.reportsMade | r in a.notification iff (r.position = a.city.position)
}

fact statisticsVisualization{
    all u : User, v : ViolationVisualizer | (u = Authority implies v = ViolationVisualizerPro else v = ViolationVisualizerLimited)
}

fact statistics{
    all v : ViolationVisualizer | #v.violation>0 iff (some u : User | #u.reportsMade>0)
}

fact suggestionsActivation{
    all s : SuggestionInferralEngine, v : Violation | #s.suggestions>0 iff (#s.municipalities>0 and #v>0)
}

fact MunicipalityDataProvided{
    all s : SuggestionInferralEngine | (#s.municipalities>0 and (some u : User | #u.reportsMade>0)) 
    implies (some a : Authority | s.suggestions in a.suggestions)
}
@using $rootnamespace$.Models
@{
    var data = ((WelcomeMemberModel)ViewBag.Data);
}

<p>Dear @data.Name,</p>
<span>We apreciate that you are now part of our team. Contact us if you need something.</span>

<table>
    <tr>
        <td>Username</td>
        <td><b>@data.Username</b></td>
    </tr>
    <tr>
        <td>Password</td>
        <td><b>@data.Password</b></td>
    </tr>
</table>
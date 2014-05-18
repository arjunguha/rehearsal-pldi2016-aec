@{
    var data = ((ForgotPasswordResetModel) ViewBag.Data);
}

@using $rootnamespace$.Models

Dear @data.FirstName,

A new password has been requested.  Here is a temporary password you can use to logon to the site.

<table>
    <tr>
        <td>Username</td>
        <td>@data.UserName</td>
    </tr>
    <tr>
        <td>Password</td>
        <td>@data.TemporaryPassword</td>
    </tr>
    <tr>
        <td>Login Url</td>
        <td>@data.LoginUrl</td>
    </tr>
</table>
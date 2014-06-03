@model $rootnamespace$.Core.Model.Customer

<table class="table table-bordered">
    <tr>
        <th>ID</th>
        <th>Created</th>
    </tr>
    <tr>
        <td>@Model.Id</td>
        <td>@Model.Created</td>
    </tr>
</table>

<table class="table table-bordered">
    <tr>
        <th style="width: 200px">
            Full Name
        </th>
        <td>
            @Model.FullName
        </td>
    </tr>
    <tr>
        <th>
            Email Address
        </th>
        <td>
            @Model.EmailAddress
        </td>
    </tr>
    <tr>
        <th>
            Mailing Address
        </th>
        <td>
           @Model.Address
        </td>
    </tr>
    <tr>
        <th>
            City
        </th>
        <td>
            @Model.City
        </td>
    </tr>
    <tr>
        <th>
            State
        </th>
        <td>
            @Model.State
        </td>
    </tr>
        <tr>
        <th>
            Country
        </th>
        <td>
           @Model.Country
        </td>
    </tr>
</table>

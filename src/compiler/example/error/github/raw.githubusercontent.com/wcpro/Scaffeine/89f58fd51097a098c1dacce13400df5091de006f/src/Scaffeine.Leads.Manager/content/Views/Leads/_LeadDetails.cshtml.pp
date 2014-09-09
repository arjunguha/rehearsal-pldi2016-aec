@model $rootnamespace$.Core.Model.Lead

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
            Source
        </th>
        <td>
           @Model.Source 
        </td>
    </tr>
    <tr>
        <th style="width: 200px">
            Browser
        </th>
        <td>
            @Model.Browser
        </td>
    </tr>
    <tr>
        <th style="width: 200px">
            IP Address
        </th>
        <td>
            @Model.IPAddress 
        </td>
    </tr>
    <tr>
        <th style="width: 200px">
            Campaign ID
        </th>
        <td>
            @Model.CampaignId 
        </td>
    </tr>
    <tr>
        <th style="width: 200px">
            Campaign SubID
        </th>
        <td>
            @Model.SubId 
        </td>
    </tr>
     <tr>
        <th style="width: 200px">
            Session ID
        </th>
        <td>
           @Model.SessionId.ToUpper()
        </td>
    </tr>
</table>

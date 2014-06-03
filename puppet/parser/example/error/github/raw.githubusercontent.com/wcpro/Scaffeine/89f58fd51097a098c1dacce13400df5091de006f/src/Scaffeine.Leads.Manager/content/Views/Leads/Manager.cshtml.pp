@{
    ViewBag.Title = "Leads";
    ViewBag.SitemapProvider = "Modules";
    Layout = "~/Views/Shared/_Folder.cshtml";
}
@model $rootnamespace$.Core.Interfaces.Paging.IPage<$rootnamespace$.Core.Model.Lead>

<table class="table table-bordered">
    
    @if (this.Model.Entities.Any())
    {
        <thead>
            <tr>
                <th>Id</th>                
                <th>Customer Name</th>
                <th style="text-align: right">Order Total</th>
                <th>Source</th>
                <th>Lead Status</th>
                <th>Created</th>             
               
            </tr>
        </thead>
        
        foreach (var customer in Model.Entities)
        {
            <tr>
                <td><a href="@Url.Action("Record", "Leads", new { id = customer.Id })">@customer.Id</a></td>
                <td>@customer.Customer.FullName</td>  
                <td style="text-align: right">@customer.Order.OrderTotal.ToString("c")</td>            
                <td>@customer.Source</td>               
                <td><a href="#">@customer.Order.OrderStatus</a></td>   
                <td>@customer.Created</td>            
                
            </tr>
        }

    }
    else
    {
        <tr>
            <td style="text-align: center">
                <em>There are no leads created yet.  Leads must be created from an external source (See the API Information)</em>
            </td>
        </tr>
    }
    

</table>
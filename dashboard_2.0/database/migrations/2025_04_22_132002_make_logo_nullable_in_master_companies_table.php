<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if (Schema::hasColumn('master_companies', 'logo')) {
            Schema::table('master_companies', function (Blueprint $table) {
                $table->string('logo')->nullable()->change();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        if (Schema::hasColumn('master_companies', 'logo')) {
            Schema::table('master_companies', function (Blueprint $table) {
                $table->string('logo')->nullable(false)->change();
            });
        }
    }
};
